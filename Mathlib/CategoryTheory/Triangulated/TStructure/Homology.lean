/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.Shift
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ULift
public import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFour

/-!
# Homology for a t-structure

-/

@[expose] public section

universe v v'

open CategoryTheory Category Limits Pretriangulated Preadditive ZeroObject

namespace CategoryTheory

namespace Limits

namespace CokernelCofork

variable {C : Type*} [Category C] [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
lemma nonempty_isColimit_iff_preadditiveYoneda {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) :
    Nonempty (IsColimit c) ↔ ∀ (A : C), ((ShortComplex.mk _ _ c.condition).op.map
      (preadditiveYoneda.obj A)).Exact ∧
      Mono (((ShortComplex.mk _ _ c.condition).op.map (preadditiveYoneda.obj A)).f) := by
  simp_rw [ShortComplex.ab_exact_iff, AddCommGrpCat.mono_iff_injective]
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

lemma nonempty_isLimit_iff_preadditiveCoyoneda {X Y : C} {f : X ⟶ Y} (c : KernelFork f) :
    Nonempty (IsLimit c) ↔ ∀ (A : C), ((ShortComplex.mk _ _ c.condition).map
      (preadditiveCoyoneda.obj (Opposite.op A))).Exact ∧
      Mono (((ShortComplex.mk _ _ c.condition).map (preadditiveCoyoneda.obj
        (Opposite.op A))).f) := by
  simp_rw [ShortComplex.ab_exact_iff, AddCommGrpCat.mono_iff_injective]
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

set_option backward.isDefEq.respectTransparency false in
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

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H]
  (i : C ⥤ D) [Full i] [Faithful i]

noncomputable def preimageNatTrans {F₁ F₂ : H ⥤ C} (τ : F₁ ⋙ i ⟶ F₂ ⋙ i) : F₁ ⟶ F₂ where
  app X := i.preimage (τ.app X)
  naturality {X Y} f := i.map_injective (by
    simp only [map_comp, map_preimage]
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
noncomputable def preimageNatIso {F₁ F₂ : H ⥤ C} (e : F₁ ⋙ i ≅ F₂ ⋙ i) : F₁ ≅ F₂ where
  hom := i.preimageNatTrans e.hom
  inv := i.preimageNatTrans e.inv

lemma isEquivalenceFullSubcategoryLift (S : ObjectProperty D) (hi : i.essImage = S) :
    IsEquivalence (S.lift i
      (fun X => by rw [← hi]; exact obj_mem_essImage i X)) := by
  let F := S.lift i
      (fun X => by rw [← hi]; exact obj_mem_essImage i X)
  have : Full F := ⟨fun f ↦ ⟨i.preimage f.hom, by cat_disch⟩⟩
  have : Faithful F := ⟨fun {X Y} f g h => i.map_injective ((ObjectProperty.ι _).congr_map h)⟩
  have : EssSurj F := ⟨by
    rintro ⟨X, hX⟩
    rw [← hi] at hX
    obtain ⟨Y, ⟨e⟩⟩ := hX
    exact ⟨Y, ⟨S.ι.preimageIso e⟩⟩⟩
  exact { }

end Functor

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C) [IsTriangulated C]

lemma truncLE₀GE₀_mem_heart (X : C) :
    t.heart ((t.truncLEGE 0 0).obj X) := by
  rw [t.mem_heart_iff]
  dsimp [truncLEGE]
  constructor
  · infer_instance
  · infer_instance

lemma truncGE₀LE₀_mem_heart (X : C) :
    t.heart ((t.truncGELE 0 0).obj X) := by
  rw [t.mem_heart_iff]
  constructor <;> infer_instance

variable {H : Type*} [Category H] [Preadditive H] [t.Heart H]

variable (H) in
class HasHomology₀ where
  homology₀ : C ⥤ H
  iso : homology₀ ⋙ t.ιHeart ≅ t.truncGELE 0 0

@[implicit_reducible]
noncomputable def hasHomology₀ : t.HasHomology₀ H where
  homology₀ := t.liftHeart (t.truncGELE 0 0) t.truncGE₀LE₀_mem_heart
  iso := t.liftHeartιHeart _ _ _

variable [ht : t.HasHomology₀ H]

def homology₀ : C ⥤ H := ht.homology₀

def homology₀ιHeart : t.homology₀ ⋙ t.ιHeart (H := H) ≅ t.truncGELE 0 0 := ht.iso

end TStructure

end Triangulated

namespace ObjectProperty

open Triangulated

variable (S : ObjectProperty C) [S.IsTriangulated] (t : TStructure C)
  [S.HasInducedTStructure t]
  {H : Type*} [Category H] [Preadditive H] [t.Heart H]

instance : S.ι.TExact (S.tStructure t) t where
  rightTExact := ⟨fun _ _ ⟨hX⟩ => ⟨hX⟩⟩
  leftTExact := ⟨fun _ _ ⟨hX⟩ => ⟨hX⟩⟩

class ContainsHeart : Prop where
  subset : t.heart ≤ S

variable [hS : S.ContainsHeart t]

noncomputable instance : (S.tStructure t).Heart H where
  ι := S.lift t.ιHeart (fun X => hS.subset _ (t.ιHeart_obj_mem X))
  essImage_eq_heart := by
    ext X
    constructor
    · rintro ⟨Y, ⟨e⟩⟩
      exact prop_of_iso t.heart (S.ι.mapIso e)
        (t.ιHeart_obj_mem Y)
    · intro hX
      exact ⟨_, ⟨S.ι.preimageIso (t.ιHeartObjHeartMkIso _ hX)⟩⟩

noncomputable def ιHeartIso : (S.tStructure t).ιHeart ⋙ S.ι ≅ t.ιHeart (H := H) := Iso.refl _

variable [t.HasHomology₀ H]

noncomputable instance : (S.tStructure t).HasHomology₀ H where
  homology₀ := S.ι ⋙ t.homology₀
  iso := S.ι.preimageNatIso (Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (S.ιHeartIso t) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ t.homology₀ιHeart ≪≫
      (S.ι.truncGELEIso (S.tStructure t) t 0 0).symm)

noncomputable instance [(t.homology₀ (H := H)).ShiftSequence ℤ] :
    ((S.tStructure t).homology₀ (H := H)).ShiftSequence ℤ :=
  (inferInstance : (S.ι ⋙ t.homology₀).ShiftSequence ℤ)

instance : t.plus.ContainsHeart t where
  subset _ hX := ⟨0, ⟨hX.2⟩⟩

instance : t.minus.ContainsHeart t where
  subset _ hX := ⟨0, ⟨hX.1⟩⟩

instance : t.bounded.ContainsHeart t where
  subset _ hX := ⟨⟨0, ⟨hX.2⟩⟩, ⟨0, ⟨hX.1⟩⟩⟩

end ObjectProperty

namespace Triangulated

namespace TStructure

variable (t : TStructure C) [IsTriangulated C]

noncomputable abbrev tPlus := t.plus.tStructure t
noncomputable abbrev tMinus := t.minus.tStructure t
noncomputable abbrev tBounded := t.bounded.tStructure t

section

omit [IsTriangulated C] in
lemma zero_mem_heart : t.heart 0 := by
  rw [t.mem_heart_iff]
  constructor <;> infer_instance

omit [IsTriangulated C] in
lemma prod_mem_heart (X₁ X₂ : C) (hX₁ : t.heart X₁) (hX₂ : t.heart X₂) :
    t.heart (X₁ ⨯ X₂) := by
  rw [t.mem_heart_iff]
  constructor
  · exact t.isLE₂ _ (binaryProductTriangle_distinguished X₁ X₂) 0 ⟨hX₁.1⟩ ⟨hX₂.1⟩
  · exact t.isGE₂ _ (binaryProductTriangle_distinguished X₁ X₂) 0 ⟨hX₁.2⟩ ⟨hX₂.2⟩

instance : HasTerminal t.heart.FullSubcategory := by
  let Z : t.heart.FullSubcategory  := ⟨0, t.zero_mem_heart⟩
  have : ∀ X, Inhabited (X ⟶ Z) := fun X => ⟨0⟩
  have : ∀ X, Unique (X ⟶ Z) := fun X =>
    { uniq := fun f => t.heart.ι.map_injective
        ((isZero_zero C).eq_of_tgt _ _) }
  exact hasTerminal_of_unique Z

instance : t.heart.IsClosedUnderLimitsOfShape (Discrete WalkingPair) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    apply t.heart.prop_of_iso (limit.isoLimitCone ⟨_, (IsLimit.postcomposeHomEquiv
      (diagramIsoPair p.diag) _).symm p.isLimit⟩)
    exact (prod_mem_heart t _ _ (p.prop_diag_obj _) (p.prop_diag_obj _))

instance : HasFiniteProducts t.heart.FullSubcategory :=
  hasFiniteProducts_of_has_binary_and_terminal

variable (H : Type*) [Category* H] [Preadditive H] [t.Heart H]

noncomputable def heartEquivalenceFullsubcategory :
    H ≌ t.heart.FullSubcategory :=
  have := t.ιHeart.isEquivalenceFullSubcategoryLift t.heart (by
    ext X
    rw [t.mem_essImage_ιHeart_iff])
  @Functor.asEquivalence _ _ _ _ _ this

include t in
omit [IsTriangulated C] in
lemma hasFiniteProducts_heart : HasFiniteProducts H where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence
      (t.heartEquivalenceFullsubcategory H).functor

instance (X : C) (n : ℤ) [t.IsGE X 0] : t.IsGE (X⟦n⟧) (-n) :=
  t.isGE_shift X 0 n (-n) (by linarith)

instance (X : C) (n : ℤ) [t.IsGE X 0] : t.IsGE (X⟦-n⟧) n :=
  t.isGE_shift X 0 (-n) n (by linarith)

instance (X : C) (n : ℤ) [t.IsLE X 0] : t.IsLE (X⟦n⟧) (-n) :=
  t.isLE_shift X 0 n (-n) (by linarith)

instance (X : C) (n : ℤ) [t.IsLE X 0] : t.IsLE (X⟦-n⟧) n :=
  t.isLE_shift X 0 (-n) n (by linarith)

instance (X : C) [t.IsLE X 0] : t.IsLE X 1 :=
  t.isLE_of_le X 0 1 (by linarith)

instance (X : C) (n : ℤ) [t.IsLE X n] : t.IsLE (X⟦(1 : ℤ)⟧) n :=
  have := t.isLE_shift X n 1 (n - 1) (by linarith)
  t.isLE_of_le (X⟦(1 : ℤ)⟧) (n - 1) n (by linarith)

instance (X : C) [t.IsGE X 0] : t.IsGE X (-1) :=
  t.isGE_of_ge X (-1) 0 (by linarith)

instance (X : C) (n : ℤ) [t.IsLE X n] : t.IsLE (X⟦n⟧) 0 :=
  t.isLE_shift X n n 0 (add_zero n)

instance (X : C) (n : ℤ) [t.IsGE X n] : t.IsGE (X⟦n⟧) 0 :=
  t.isGE_shift X n n 0 (add_zero n)

instance (X : C) : t.IsLE ((t.truncLT 0).obj X) (-1) :=
  t.isLE_of_iso ((t.truncLEIsoTruncLT (-1) 0 (by linarith)).app X) (-1)

section

variable {X₁ X₂ : H} {X₃ : C} {f₁ : X₁ ⟶ X₂} {f₂ : t.ιHeart.obj X₂ ⟶ X₃}
    {f₃ : X₃ ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (t.ιHeart.map f₁) f₂ f₃ ∈ distTriang C)

omit [IsTriangulated C]
include hT

lemma cocone_heart_isLE_zero : t.IsLE X₃ 0 :=
  t.isLE₂ _ (rot_of_distTriang _ hT) 0 (by dsimp; infer_instance)
    (by dsimp; infer_instance)

lemma cocone_heart_isGE_neg_one : t.IsGE X₃ (-1) :=
  t.isGE₂ _ (rot_of_distTriang _ hT) (-1)
    (by dsimp; infer_instance) (by dsimp; infer_instance)

end

set_option backward.isDefEq.respectTransparency false in
lemma exists_distinguished_triangle_of_isLE_zero_of_isGE_neg_one
    (X : C) [t.IsLE X 0] [t.IsGE X (-1)] :
    ∃ (K Q : H) (α : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ⟶ X) (β : X ⟶ t.ιHeart.obj Q)
      (γ : t.ιHeart.obj Q ⟶ (t.ιHeart.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang C := by
  have hK : t.heart (((t.truncLE (-1)).obj X)⟦(-1 : ℤ)⟧) := by
    rw [t.mem_heart_iff]
    constructor <;> dsimp <;> infer_instance
  have hQ : t.heart ((t.truncGE 0).obj X) := by
    rw [t.mem_heart_iff]
    constructor <;> infer_instance
  have e₁ := (shiftFunctor C (1 : ℤ)).mapIso (t.ιHeartObjHeartMkIso (H := H) _ hK) ≪≫
    (shiftEquiv C (1 : ℤ)).counitIso.app _
  have e₃ := t.ιHeartObjHeartMkIso (H := H) _ hQ
  refine ⟨t.heartMk _ hK, t.heartMk _ hQ, e₁.hom ≫ (t.truncLEι (-1)).app X,
    (t.truncGEπ 0).app X ≫ e₃.inv,
    e₃.hom ≫ (t.truncGEδLE (-1) 0 (by linarith)).app X ≫ e₁.inv⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ (t.triangleLEGE_distinguished (-1) 0 (by linarith) X) _ ?_
  refine Triangle.isoMk _ _ e₁ (Iso.refl _) e₃ ?_ ?_ ?_
  · dsimp
    simp
  · dsimp
    simp
  · dsimp
    simp only [Category.assoc, ← Functor.map_comp,
      e₁.inv_hom_id, Functor.id_obj, Functor.map_id, Category.comp_id]

lemma admissibleMorphism_ιHeart {X₁ X₂ : H} (f : X₁ ⟶ X₂) :
    AbelianSubcategory.admissibleMorphism (t.ιHeart (H := H)) f := by
  intro X₃ f₂ f₃ hT
  have := t.cocone_heart_isLE_zero H hT
  have := t.cocone_heart_isGE_neg_one H hT
  exact t.exists_distinguished_triangle_of_isLE_zero_of_isGE_neg_one H X₃

noncomputable abbrev abelianHeart : Abelian H := by
  letI := t.hasFiniteProducts_heart H
  refine AbelianSubcategory.abelian (t.ιHeart (H := H)) ?_ ?_
  · intro X Y n f hn
    exact t.zero f 0 (-n) (by linarith)
  · ext
    simp only [MorphismProperty.top_apply, iff_true]
    apply admissibleMorphism_ιHeart

end

section

variable {H : Type*} [Category* H] [Preadditive H] [t.Heart H] [t.HasHomology₀ H]

section

variable (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) [t.IsLE T.obj₁ n]

@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def truncLETriangle :
    Triangle C :=
  Triangle.mk ((t.truncLE n).map T.mor₁)
    ((t.truncLE n).map T.mor₂)
    ((t.truncLEι n).app T.obj₃ ≫ T.mor₃ ≫ (asIso ((t.truncLEι n).app T.obj₁)).inv⟦(1 : ℤ)⟧')

instance : t.IsLE (t.truncLETriangle T n).obj₁ n := by dsimp; infer_instance
instance : t.IsLE (t.truncLETriangle T n).obj₂ n := by dsimp; infer_instance
instance : t.IsLE (t.truncLETriangle T n).obj₃ n := by dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
include hT in
lemma truncLETriangle_distinguished :
    t.truncLETriangle T n ∈ distTriang C := by
  let a : T.obj₁ ⟶ (t.truncLE n).obj T.obj₂ :=
    (asIso ((t.truncLEι n).app T.obj₁)).inv ≫ (t.truncLE n).map T.mor₁
  let b := (t.truncLEι n).app T.obj₂
  have comm : a ≫ b = T.mor₁ := by simp [a, b]
  obtain ⟨Z, f₂, f₃, h₁⟩ := distinguished_cocone_triangle a
  have h₂ := (t.triangleLEGT_distinguished n T.obj₂)
  have H := someOctahedron comm h₁ h₂ hT
  have : t.IsLE Z n := t.isLE₂ _ (rot_of_distTriang _ h₁) n
      (by dsimp; infer_instance) (by dsimp; infer_instance)
  obtain ⟨e, he : e.hom.hom₂ = 𝟙 _⟩ :=
    t.triangle_iso_exists
      (t.triangleLEGE_distinguished n (n + 1) rfl T.obj₃) H.mem (Iso.refl _) n (n + 1)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
  have he' : e.inv.hom₂ = 𝟙 _ := by
    rw [← cancel_mono e.hom.hom₂, ← comp_hom₂, e.inv_hom_id, id_hom₂, he, comp_id]
  have he₁' : (truncLE t n).map T.mor₂ = f₂ ≫ e.inv.hom₁ := by
    apply to_truncLE_obj_ext
    have eq₁ := e.inv.comm₁
    have eq₂ := H.comm₁
    dsimp at eq₁ eq₂ ⊢
    rw [NatTrans.naturality, Functor.id_map, ← eq₂, assoc, ← eq₁, he']
    simp
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
  refine isomorphic_distinguished _ h₁ _ ?_
  exact Triangle.isoMk _ _ (asIso ((t.truncLEι n).app T.obj₁))
    (Iso.refl _) (Triangle.π₁.mapIso e) (by simp [a]) (by simp [he₁]) he₂

end

section

variable (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) [t.IsGE T.obj₃ n]

@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def truncGETriangle :
    Triangle C :=
  Triangle.mk ((t.truncGE n).map T.mor₁) ((t.truncGE n).map T.mor₂)
    ((asIso ((t.truncGEπ n).app T.obj₃)).inv ≫ T.mor₃ ≫ ((t.truncGEπ n).app T.obj₁)⟦(1 : ℤ)⟧')

instance : t.IsGE (t.truncGETriangle T n).obj₁ n := by dsimp; infer_instance
instance : t.IsGE (t.truncGETriangle T n).obj₂ n := by dsimp; infer_instance
instance : t.IsGE (t.truncGETriangle T n).obj₃ n := by dsimp; infer_instance

instance (X : C) [t.IsGE X n] : t.IsGE (X⟦(-1 : ℤ)⟧) n := by
  have : t.IsGE (X⟦(-1 : ℤ)⟧) (n + 1) :=
    t.isGE_shift X n (-1) (n + 1) (by linarith)
  exact t.isGE_of_ge _ n (n + 1) (by linarith)

set_option backward.isDefEq.respectTransparency false in
include hT in
lemma truncGETriangle_distinguished :
    t.truncGETriangle T n ∈ distTriang C := by
  let a := (t.truncGEπ n).app T.obj₂
  let b : (t.truncGE n).obj T.obj₂ ⟶ T.obj₃ :=
    (t.truncGE n).map T.mor₂ ≫ (asIso ((t.truncGEπ n).app T.obj₃)).inv
  have comm : a ≫ b = T.mor₂ := by simp [a, b]
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
    refine isomorphic_distinguished _ H.mem _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (-(Iso.refl _)) (Iso.refl _) ?_ ?_ ?_
    · dsimp
      simp [hm₁, T']
    · dsimp
      simp [hm₃, T']
    · dsimp
      simp [T']
  have : t.IsGE Z n := t.isGE₂ _ (inv_rot_of_distTriang _ h₂) n
    (by dsimp; infer_instance) (by dsimp; infer_instance)
  obtain ⟨e, he : _ = 𝟙 _⟩ :=
    t.triangle_iso_exists (t.triangleLEGE_distinguished (n - 1) n (by linarith) T.obj₁)
      Hmem' (Iso.refl _) (n-1) n
      (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp [T']; infer_instance) (by dsimp [T']; infer_instance)
  refine isomorphic_distinguished _ h₂ _ ?_
  refine Triangle.isoMk _ _ (Triangle.π₃.mapIso e) (Iso.refl _)
    (asIso ((t.truncGEπ n).app T.obj₃)).symm ?_ ?_ ?_
  · dsimp
    simp only [comp_id]
    have eq₁ := e.hom.comm₂
    have eq₂ := H.comm₄
    dsimp [a] at eq₁ eq₂
    simp only [neg_comp, comp_neg, neg_inj] at eq₂
    apply from_truncGE_obj_ext
    rw [reassoc_of% eq₁, he]
    dsimp
    rw [id_comp, ← NatTrans.naturality]
    dsimp [T']
    apply (shiftFunctor C (1 : ℤ)).map_injective
    simpa only [Functor.map_comp, hm₃] using eq₂
  · dsimp
    simp [b]
  · dsimp [truncGETriangle]
    simp only [assoc, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc]
    have eq₁ := H.comm₃
    have eq₂ := e.hom.comm₂
    dsimp at eq₁ eq₂
    rw [← eq₁, ← Functor.map_comp, eq₂, he]
    dsimp [T']
    rw [id_comp, hm₃]

end

set_option backward.isDefEq.respectTransparency false in
noncomputable def toHomology₀ (X : C) [t.IsLE X 0] :
    X ⟶ t.ιHeart.obj ((t.homology₀ (H := H)).obj X) :=
  inv ((t.truncLEι 0).app X) ≫ (t.truncGEπ 0).app _ ≫ t.homology₀ιHeart.inv.app X

omit [IsTriangulated C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toHomology₀_naturality {X Y : C} (f : X ⟶ Y) [t.IsLE X 0] [t.IsLE Y 0] :
    t.toHomology₀ (H := H) X ≫ t.ιHeart.map (t.homology₀.map f) = f ≫ t.toHomology₀ Y := by
  dsimp [toHomology₀]
  rw [← cancel_epi ((t.truncLEι 0).app X), assoc, assoc, IsIso.hom_inv_id_assoc]
  erw [← NatTrans.naturality, ← NatTrans.naturality_assoc,
    ← NatTrans.naturality_assoc, IsIso.hom_inv_id_assoc]
  rfl

instance (A X : C) [t.IsLE X 0] [t.IsGE A 0] :
    IsIso ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) := by
  have : Mono ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) :=
    (preadditiveYoneda_map_distinguished _
      (rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X)) A).mono_g (by
      apply IsZero.eq_of_src
      apply AddCommGrpCat.isZero
      intro (x : ((t.truncLT 0).obj X)⟦(1 : ℤ)⟧ ⟶ A)
      have : t.IsLE (((t.truncLT 0).obj X)⟦(1 : ℤ)⟧) (-1) :=
        t.isLE_shift ((t.truncLT 0).obj X) 0 1 (-1) (by linarith)
      exact t.zero x (-1) 0 (by linarith))
  have : Epi ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) :=
    (preadditiveYoneda_map_distinguished _ (t.triangleLTGE_distinguished 0 X) A).epi_f (by
      apply IsZero.eq_of_tgt
      apply AddCommGrpCat.isZero
      intro (x : (t.truncLT 0).obj X ⟶ A)
      exact t.zero x (-1) 0 (by linarith))
  apply isIso_of_mono_of_epi

set_option backward.isDefEq.respectTransparency false in
instance (A X : C) [t.IsLE X 0] [t.IsGE A 0] :
    IsIso ((preadditiveYoneda.obj A).map (t.toHomology₀ (H := H) X).op) := by
  dsimp only [toHomology₀]
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
noncomputable def fromHomology₀ (X : C) [t.IsGE X 0] :
    t.ιHeart.obj (t.homology₀ (H := H).obj X) ⟶ X :=
  t.homology₀ιHeart.hom.app X ≫ (t.truncGELEIsoLEGE 0 0).hom.app X ≫ (t.truncLEι 0).app _ ≫
    inv ((t.truncGEπ 0).app X)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma fromHomology₀_naturality {X Y : C} (f : X ⟶ Y) [t.IsGE X 0] [t.IsGE Y 0] :
    t.ιHeart.map (t.homology₀.map f) ≫ t.fromHomology₀ (H := H) Y = t.fromHomology₀ X ≫ f := by
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
        apply AddCommGrpCat.isZero
        intro (x : A ⟶ (((t.truncGE 1).obj X)⟦(-1 : ℤ)⟧))
        have : t.IsGE (((t.truncGE 1).obj X)⟦(-1 : ℤ)⟧) 1 :=
          t.isGE_shift ((t.truncGE 1).obj X) 0 (-1) 1 (by linarith)
        exact t.zero x 0 1 (by linarith))
  have : Epi ((preadditiveCoyoneda.obj (Opposite.op A)).map ((t.truncLEι 0).app X)) :=
    ((preadditiveCoyoneda.obj (Opposite.op A)).map_distinguished_exact _
      (t.triangleLEGE_distinguished 0 1 (by linarith) X)).epi_f (by
        apply IsZero.eq_of_tgt
        apply AddCommGrpCat.isZero
        intro (x : A ⟶ (t.truncGE 1).obj X)
        exact t.zero x 0 1 (by linarith))
  apply isIso_of_mono_of_epi

set_option backward.isDefEq.respectTransparency false in
instance (A X : C) [t.IsGE X 0] [t.IsLE A 0] :
    IsIso ((preadditiveCoyoneda.obj (Opposite.op A)).map (t.fromHomology₀ (H := H) X)) := by
  dsimp only [fromHomology₀]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : (t.homology₀ (H := H)).Additive := by
  have := Functor.additive_of_iso (t.homology₀ιHeart (H := H)).symm
  refine ⟨fun {X Y f g} => t.ιHeart.map_injective ?_⟩
  erw [(t.homology₀ ⋙ t.ιHeart).map_add]
  simp

omit [IsTriangulated C] in
lemma isIso_homology₀_iff_isIso_truncGE₀LE₀_map {X Y : C} (f : X ⟶ Y) :
    IsIso ((t.homology₀ (H := H)).map f) ↔ IsIso ((t.truncGELE 0 0).map f) := by
  have : IsIso ((t.homology₀ (H := H)).map f) ↔
    IsIso (t.ιHeart.map ((t.homology₀ (H := H)).map f)) := by
    constructor
    · intro h
      infer_instance
    · intro h
      apply isIso_of_reflects_iso  _ t.ιHeart
  rw [this]
  exact NatIso.isIso_map_iff t.homology₀ιHeart f

lemma isIso_homology₀_iff_isIso_truncLE₀GE₀_map {X Y : C} (f : X ⟶ Y) :
    IsIso ((t.homology₀ (H := H)).map f) ↔ IsIso ((t.truncLEGE 0 0).map f) := by
  rw [isIso_homology₀_iff_isIso_truncGE₀LE₀_map]
  exact NatIso.isIso_map_iff (t.truncGELEIsoLEGE 0 0) f

set_option backward.isDefEq.respectTransparency false in
instance (X : C) : IsIso ((t.homology₀ (H := H)).map ((truncLEι t 0).app X)) := by
  rw [isIso_homology₀_iff_isIso_truncGE₀LE₀_map]
  dsimp [truncGELE]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance (X : C) : IsIso ((t.homology₀ (H := H)).map ((truncGEπ t 0).app X)) := by
  rw [isIso_homology₀_iff_isIso_truncLE₀GE₀_map]
  dsimp [truncLEGE]
  infer_instance

end

section

variable {H : Type*} [Category* H] [Abelian H] [t.Heart H] [t.HasHomology₀ H]

namespace IsHomologicalAux

variable {T : Triangle C} (hT : T ∈ distTriang C)

@[simps!]
noncomputable def shortComplex :=
  (ShortComplex.mk _ _ (comp_distTriang_mor_zero₁₂ T hT)).map (t.homology₀ (H := H))

@[simps]
noncomputable def ιHeartAddEquiv (X Y : H) :
    (X ⟶ Y) ≃+ (t.ιHeart.obj X ⟶ t.ιHeart.obj Y) where
  toFun f := t.ιHeart.map f
  invFun g := t.ιHeart.preimage g
  left_inv f := by simp
  right_inv g := by simp
  map_add' := by aesop_cat

noncomputable def addEquivFromHomology₀OfIsLE (X : C) [t.IsLE X 0] (A : H) :
    (t.homology₀.obj X ⟶ A) ≃+ (X ⟶ t.ιHeart.obj A)  :=
  (ιHeartAddEquiv _ _ _).trans
    (asIso ((preadditiveYoneda.obj
      (t.ιHeart.obj A)).map (t.toHomology₀ _).op)).addCommGroupIsoToAddEquiv

omit [IsTriangulated C] in
lemma addEquivFromHomology₀OfIsLE_naturality {X Y : C} (f : X ⟶ Y)
    [t.IsLE X 0] [t.IsLE Y 0] (A : H) (y : t.homology₀.obj Y ⟶ A) :
    f ≫ addEquivFromHomology₀OfIsLE t Y A y =
      addEquivFromHomology₀OfIsLE t X A (t.homology₀.map f ≫ y) := by
  change f ≫ t.toHomology₀ Y ≫ t.ιHeart.map y =
    t.toHomology₀ X ≫ t.ιHeart.map (t.homology₀.map f ≫ y)
  simp only [Functor.map_comp, toHomology₀_naturality_assoc]

omit [IsTriangulated C] in
lemma case₁ [t.IsLE T.obj₁ 0] [t.IsLE T.obj₂ 0] [t.IsLE T.obj₃ 0] :
    (shortComplex t (H := H) hT).Exact ∧ Epi (shortComplex t (H := H) hT).g := by
  rw [ShortComplex.exact_and_epi_g_iff_preadditiveYoneda]
  intro A
  let S := (shortComplex t hT).op.map (preadditiveYoneda.obj A)
  let S' := (ShortComplex.mk _ _ (comp_distTriang_mor_zero₁₂ T hT)).op.map
    (preadditiveYoneda.obj (t.ιHeart.obj A))
  refine (ShortComplex.exact_and_mono_f_iff_of_addEquiv S S'
    (addEquivFromHomology₀OfIsLE t T.obj₃ A) (addEquivFromHomology₀OfIsLE t T.obj₂ A)
    (addEquivFromHomology₀OfIsLE t T.obj₁ A) (addEquivFromHomology₀OfIsLE_naturality t T.mor₂ A)
    (addEquivFromHomology₀OfIsLE_naturality t T.mor₁ A)).2 ?_
  refine ⟨preadditiveYoneda_map_distinguished _ hT (t.ιHeart.obj A),
    (preadditiveYoneda_map_distinguished _ (rot_of_distTriang _ hT) (t.ιHeart.obj A)).mono_g ?_⟩
  apply IsZero.eq_of_src
  apply AddCommGrpCat.isZero
  intro (x : T.obj₁⟦(1 : ℤ)⟧ ⟶ t.ιHeart.obj A)
  exact t.zero x (-1) 0 (by linarith)

set_option backward.isDefEq.respectTransparency false in
lemma case₂ (h₁ : t.IsLE T.obj₁ 0) :
    (shortComplex t (H := H) hT).Exact ∧ Epi (shortComplex t (H := H) hT).g := by
  have h' := case₁ t (H := H) (t.truncLETriangle_distinguished T hT 0)
  refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).1 h'
  refine ShortComplex.isoMk
    (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₁)))
    (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₂)))
    (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₃))) ?_ ?_
  all_goals
    dsimp
    simp only [← Functor.map_comp, NatTrans.naturality, Functor.id_obj, Functor.id_map]

noncomputable def addEquivToHomology₀OfIsGE (X : C) [t.IsGE X 0] (A : H) :
    (A ⟶ t.homology₀.obj X) ≃+ (t.ιHeart.obj A ⟶ X) := by
  exact (ιHeartAddEquiv _ _ _).trans
    (asIso ((preadditiveCoyoneda.obj (Opposite.op (t.ιHeart.obj A))).map
      (t.fromHomology₀ X))).addCommGroupIsoToAddEquiv

lemma addEquivToHomology₀OfIsGE_naturality {X Y : C} (f : X ⟶ Y)
    [t.IsGE X 0] [t.IsGE Y 0] (A : H) (x : A ⟶ t.homology₀.obj X) :
    addEquivToHomology₀OfIsGE t X A x ≫ f =
      addEquivToHomology₀OfIsGE t Y A (x ≫ t.homology₀.map f) := by
  change (t.ιHeart.map x ≫ t.fromHomology₀ X) ≫ f =
    t.ιHeart.map (x ≫ t.homology₀.map f) ≫ t.fromHomology₀ Y
  simp only [assoc, Functor.map_comp, fromHomology₀_naturality]

/-- case₁' -/
lemma case₁' [t.IsGE T.obj₁ 0] [t.IsGE T.obj₂ 0] [t.IsGE T.obj₃ 0] :
    (shortComplex t (H := H) hT).Exact ∧ Mono (shortComplex t (H := H) hT).f := by
  rw [ShortComplex.exact_and_mono_f_iff_preadditiveCoyoneda]
  intro A
  let S := (shortComplex t hT).map (preadditiveCoyoneda.obj (Opposite.op A))
  let S' := (ShortComplex.mk _ _ (comp_distTriang_mor_zero₁₂ T hT)).map
    (preadditiveCoyoneda.obj (Opposite.op (t.ιHeart.obj A)))
  refine (ShortComplex.exact_and_mono_f_iff_of_addEquiv S S'
    (addEquivToHomology₀OfIsGE t T.obj₁ A) (addEquivToHomology₀OfIsGE t T.obj₂ A)
    (addEquivToHomology₀OfIsGE t T.obj₃ A)
    (addEquivToHomology₀OfIsGE_naturality t T.mor₁ A)
    (addEquivToHomology₀OfIsGE_naturality t T.mor₂ A)).2 ?_
  refine ⟨(preadditiveCoyoneda.obj (Opposite.op (t.ιHeart.obj A))).map_distinguished_exact _ hT,
    ((preadditiveCoyoneda.obj (Opposite.op (t.ιHeart.obj A))).map_distinguished_exact _
      (inv_rot_of_distTriang _ hT)).mono_g ?_⟩
  apply IsZero.eq_of_src
  apply AddCommGrpCat.isZero
  intro (x : t.ιHeart.obj A ⟶ T.obj₃⟦-1⟧)
  have : t.IsGE (T.obj₃⟦(-1 : ℤ)⟧) 1 := t.isGE_shift T.obj₃ 0 (-1) 1 (by linarith)
  exact t.zero x 0 1 (by linarith)

set_option backward.isDefEq.respectTransparency false in
/-- case₂' -/
lemma case₂' (h₃ : t.IsGE T.obj₃ 0) :
    (shortComplex t (H := H) hT).Exact ∧ Mono (shortComplex t (H := H) hT).f := by
  have h' := case₁' t (H := H) (t.truncGETriangle_distinguished T hT 0)
  refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 h'
  refine ShortComplex.isoMk
    (asIso (t.homology₀.map ((t.truncGEπ 0).app T.obj₁)))
    (asIso (t.homology₀.map ((t.truncGEπ 0).app T.obj₂)))
    (asIso (t.homology₀.map ((t.truncGEπ 0).app T.obj₃))) ?_ ?_
  all_goals
    dsimp
    simp only [← Functor.map_comp, ← NatTrans.naturality, Functor.id_map]

end IsHomologicalAux

open IsHomologicalAux

set_option backward.isDefEq.respectTransparency false in
instance : (t.homology₀ (H := H)).IsHomological where
  exact T hT := by
    have h₁ := t.triangleLEGE_distinguished 0 1 (by linarith) T.obj₁
    obtain ⟨U, f, g, h₃⟩ := distinguished_cocone_triangle ((t.truncLEι 0).app T.obj₁ ≫ T.mor₁)
    have O := someOctahedron rfl h₁ hT h₃
    have ex₁ := case₂ t (H := H) h₃ (by dsimp; infer_instance)
    have ex₂ := case₂' t (H := H) (rot_of_distTriang _ O.mem) (by dsimp; infer_instance)
    dsimp [Triangle.rotate] at ex₂
    have := ex₁.2
    have : Mono (shortComplex t (rot_of_distTriang _ O.mem)).f := ex₂.2
    have ex₃ := ShortComplex₄.connectShortComplex_exact (shortComplex t h₃)
      (shortComplex t (rot_of_distTriang _ O.mem)) (Iso.refl _)
        (t.homology₀.map T.mor₂) (by
          dsimp [shortComplex, ShortComplex.map]
          rw [id_comp, ← Functor.map_comp, O.comm₃]) ex₁.1 ex₂.1
    refine ShortComplex.exact_of_iso ?_ ex₃.exact₂
    refine ShortComplex.isoMk (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₁)))
        (Iso.refl _) (Iso.refl _) ?_ ?_
    all_goals
      dsimp; simp

variable [(t.homology₀ (H := H)).ShiftSequence ℤ]

def homology (n : ℤ) : C ⥤ H := t.homology₀.shift n

instance (n : ℤ) : (t.homology (H := H) n).Additive := by
  dsimp [homology]
  infer_instance

variable (T : Triangle C) (hT : T ∈ distTriang C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

def homologyδ : (t.homology (H := H) n₀).obj T.obj₃ ⟶ (t.homology n₁).obj T.obj₁ :=
  t.homology₀.shiftMap T.mor₃ n₀ n₁ (by linarith)

include hT in
@[reassoc (attr := simp)]
lemma homologyδ_comp : t.homologyδ T n₀ n₁ h ≫ (t.homology (H := H) n₁).map T.mor₁ = 0 :=
  t.homology₀.homologySequenceδ_comp _ hT _ _ h

include hT in
@[reassoc (attr := simp)]
lemma comp_homologyδ : (t.homology n₀).map T.mor₂ ≫ t.homologyδ (H := H) T n₀ n₁ h = 0 :=
  t.homology₀.comp_homologySequenceδ _ hT _ _ h

lemma homology_exact₁ :
    (ShortComplex.mk _ _ (t.homologyδ_comp (H := H) T hT n₀ n₁ h)).Exact :=
  t.homology₀.homologySequence_exact₁ _ hT _ _ h

lemma homology_exact₂ (n : ℤ) :
    (ShortComplex.mk ((t.homology (H := H) n).map T.mor₁) ((t.homology n).map T.mor₂)
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])).Exact :=
  t.homology₀.homologySequence_exact₂ _ hT _

lemma homology_exact₃ :
    (ShortComplex.mk _ _ (t.comp_homologyδ (H := H) T hT n₀ n₁ h)).Exact :=
  t.homology₀.homologySequence_exact₃ _ hT _ _ h

omit [IsTriangulated C] [(t.homology₀ (H := H)).ShiftSequence ℤ] in
lemma isZero_homology₀_of_isGE_one (X : C) [t.IsGE X 1] :
    IsZero (((t.homology₀ (H := H))).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply t.ιHeart.map_injective
  rw [Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero]
  refine IsZero.of_iso ?_ (t.homology₀ιHeart.app X)
  dsimp [truncGELE]
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id]
  have : IsZero ((t.truncLE 0).obj X) := by
    rw [← t.isGE_iff_isZero_truncLE_obj 0 1 (by linarith)]
    infer_instance
  rw [IsZero.iff_id_eq_zero] at this
  rw [this, Functor.map_zero]

omit [IsTriangulated C] in
lemma isZero_homology_of_isGE (X : C) (q n : ℤ) (hn₁ : q < n) [t.IsGE X n] :
    IsZero ((t.homology (H := H) q).obj X) := by
  have : t.IsGE (X⟦q⟧) (n - q) := t.isGE_shift X n q (n - q) (by linarith)
  have : t.IsGE (X⟦q⟧) 1 := t.isGE_of_ge (X⟦q⟧) 1 (n - q) (by linarith)
  exact IsZero.of_iso (t.isZero_homology₀_of_isGE_one (X⟦q⟧))
    (((t.homology₀.shiftIso q 0 q (by linarith)).app X).symm.trans
    ((t.homology₀.isoShiftZero ℤ).app (X⟦q⟧)))

omit [(t.homology₀ (H := H)).ShiftSequence ℤ] in
lemma isZero_homology₀_of_isLE_neg_one (X : C) [t.IsLE X (-1)] :
    IsZero ((t.homology₀ (H := H)).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply t.ιHeart.map_injective
  rw [Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero]
  refine IsZero.of_iso ?_ ((t.homology₀ιHeart ≪≫ t.truncGELEIsoLEGE 0 0).app X)
  dsimp [truncLEGE]
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id]
  have : IsZero ((t.truncGE 0).obj X) := by
    rw [← t.isLE_iff_isZero_truncGE_obj (-1) 0 (by linarith)]
    infer_instance
  rw [IsZero.iff_id_eq_zero] at this
  rw [this, Functor.map_zero]

lemma isZero_homology_of_isLE (X : C) (q n : ℤ) (hn₁ : n < q) [t.IsLE X n] :
    IsZero ((t.homology (H := H) q).obj X) := by
  have : t.IsLE (X⟦q⟧) (n - q) := t.isLE_shift X n q (n - q) (by linarith)
  have : t.IsLE (X⟦q⟧) (-1) := t.isLE_of_le (X⟦q⟧) (n - q) (-1) (by linarith)
  exact IsZero.of_iso (t.isZero_homology₀_of_isLE_neg_one (X⟦q⟧))
    (((t.homology₀.shiftIso q 0 q (by linarith)).app X).symm.trans
    ((t.homology₀.isoShiftZero ℤ).app (X⟦q⟧)))

set_option backward.isDefEq.respectTransparency false in
omit [(t.homology₀ (H := H)).ShiftSequence ℤ] in
lemma isGE₁_iff_isGE₀_and_isZero_homology₀ (X : C) :
    t.IsGE X 1 ↔ t.IsGE X 0 ∧ (IsZero ((t.homology₀ (H := H)).obj X)) := by
  constructor
  · intro _
    constructor
    · exact t.isGE_of_ge X 0 1 (by linarith)
    · apply isZero_homology₀_of_isGE_one
  · rintro ⟨_, hX⟩
    rw [t.isGE_iff_isZero_truncLE_obj 0 1 (by linarith)]
    rw [IsZero.iff_id_eq_zero] at hX
    replace hX := t.ιHeart.congr_map hX
    rw [Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero] at hX
    refine IsZero.of_iso hX ?_
    exact asIso ((t.truncLE 0).map ((t.truncGEπ 0).app X)) ≪≫
      (t.homology₀ιHeart ≪≫ t.truncGELEIsoLEGE 0 0).symm.app X

lemma isGE_succ_iff_isGE_and_isZero_homology (X : C) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    t.IsGE X n₁ ↔ t.IsGE X n₀ ∧ (IsZero ((t.homology (H := H) n₀).obj X)) := by
  have eq₁ : t.IsGE (X⟦n₀⟧) 1 ↔ t.IsGE X n₁ := t.isGE_shift_iff _ _ _ _ hn₁
  have eq₂ : t.IsGE (X⟦n₀⟧) 0 ↔ t.IsGE X n₀ := t.isGE_shift_iff _ _ _ _ (by linarith)
  have e : (t.homology (H := H) n₀).obj X ≅ t.homology₀.obj (X⟦n₀⟧) :=
    (t.homology₀.shiftIso n₀ 0 n₀ (add_zero n₀)).symm.app _ ≪≫
      (t.homology₀.isoShiftZero ℤ ).app _
  have eq₃ : IsZero ((t.homology n₀).obj X) ↔ IsZero (t.homology₀.obj (X⟦n₀⟧)) :=
    ⟨fun h => IsZero.of_iso h e.symm, fun h => IsZero.of_iso h e⟩
  rw [← eq₁, ←eq₂, eq₃]
  exact t.isGE₁_iff_isGE₀_and_isZero_homology₀ _

set_option backward.isDefEq.respectTransparency false in
omit [t.HasHomology₀ H] [IsTriangulated C] in
lemma isIso_whiskerLeft_ιHeart_truncLEι (b : ℤ) (hb : 0 ≤ b) :
    IsIso (Functor.whiskerLeft (t.ιHeart (H := H)) (t.truncLEι b)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  dsimp
  rw [← t.isLE_iff_isIso_truncLEι_app]
  exact t.isLE_of_le _ 0 _ hb

set_option backward.isDefEq.respectTransparency false in
omit [t.HasHomology₀ H] [IsTriangulated C] in
lemma isIso_whiskerLeft_ιHeart_truncGEπ (a : ℤ) (ha : a ≤ 0) :
    IsIso (Functor.whiskerLeft (t.ιHeart (H := H)) (t.truncGEπ a)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  dsimp
  rw [← t.isGE_iff_isIso_truncGEπ_app]
  exact t.isGE_of_ge _ _ 0 ha

set_option backward.isDefEq.respectTransparency false in
noncomputable def ιHeartTruncLE (b : ℤ) (hb : 0 ≤ b) :
    t.ιHeart (H := H) ⋙ t.truncLE b ≅ t.ιHeart :=
  have := t.isIso_whiskerLeft_ιHeart_truncLEι b hb (H := H)
  asIso (Functor.whiskerLeft t.ιHeart (t.truncLEι b))

noncomputable def ιHeartTruncGE (a : ℤ) (ha : a ≤ 0) :
    t.ιHeart (H := H) ⋙ t.truncGE a ≅ t.ιHeart :=
  have := t.isIso_whiskerLeft_ιHeart_truncGEπ a ha (H := H)
  (asIso (Functor.whiskerLeft t.ιHeart (t.truncGEπ a))).symm

noncomputable def ιHeartTruncGELE (a b : ℤ) (ha : a ≤ 0) (hb : 0 ≤ b) :
    t.ιHeart (H := H) ⋙ t.truncGELE a b ≅ t.ιHeart :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (t.ιHeartTruncLE b hb) (t.truncGE a) ≪≫ t.ιHeartTruncGE a ha

noncomputable def ιHeartHomology₀ : t.ιHeart ⋙ t.homology₀ (H := H) ≅ 𝟭 _ :=
  t.ιHeart.preimageNatIso (Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ t.homology₀ιHeart ≪≫
    t.ιHeartTruncGELE 0 0 (by rfl) (by rfl) ≪≫ (Functor.leftUnitor _).symm)

noncomputable def ιHeartHomology_zero : t.ιHeart ⋙ t.homology 0 (H := H) ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft _ (t.homology₀.isoShiftZero ℤ) ≪≫ t.ιHeartHomology₀

instance {A B : H} (f : A ⟶ B) [Mono f] (n : ℤ) :
    Mono ((t.homology (H := H) n).map (t.ιHeart.map f)) := by
  by_cases h : n = 0
  · subst h
    exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff
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

variable {H : Type*} [Category* H] [Abelian H] [t.Heart H]

lemma shortExact_of_distTriang {X₁ X₂ X₃ : H} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} (δ : t.ιHeart.obj X₃ ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧)
    (h : Triangle.mk (t.ιHeart.map f) (t.ιHeart.map g) δ ∈ distTriang C) :
    (ShortComplex.mk f g (t.ιHeart.map_injective
    (by
      rw [Functor.map_comp, Functor.map_zero]
      exact comp_distTriang_mor_zero₁₂ _ h))).ShortExact := by
  have : t.HasHomology₀ H := t.hasHomology₀
  have : (t.homology₀ (H := H)).ShiftSequence ℤ := Functor.ShiftSequence.tautological _ _
  have w : f ≫ g = 0 := t.ιHeart.map_injective (by
    simpa only [Functor.map_comp, Functor.map_zero]
      using comp_distTriang_mor_zero₁₂ _ h)
  let S := (ShortComplex.mk _ _ w).map (t.ιHeart ⋙ t.homology (H := H) 0)
  have : Mono S.f := (t.homology_exact₁ _ h (-1) 0 (by linarith)).mono_g (by
    apply IsZero.eq_of_src
    dsimp
    exact t.isZero_homology_of_isGE _ (-1) 0 (by linarith))
  have : Epi S.g := (t.homology_exact₃ _ h 0 1 (by linarith)).epi_f (by
    apply IsZero.eq_of_tgt
    dsimp
    exact t.isZero_homology_of_isLE _ 1 0 (by linarith))
  have hS : S.ShortExact := { exact := t.homology_exact₂ _ h 0 }
  refine ShortComplex.shortExact_of_iso ?_ hS
  exact ShortComplex.isoMk (t.ιHeartHomology_zero.app X₁) (t.ιHeartHomology_zero.app X₂)
    (t.ιHeartHomology_zero.app X₃) (t.ιHeartHomology_zero.hom.naturality f).symm
    (t.ιHeartHomology_zero.hom.naturality g).symm

variable (S : ShortComplex H) (hS : S.ShortExact)

include hS in
lemma exists_distTriang_of_shortExact :
    ∃ (δ : t.ιHeart.obj S.X₃ ⟶ (t.ιHeart.obj S.X₁)⟦(1 : ℤ)⟧),
      Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map S.g) δ ∈ distTriang C := by
  have : t.HasHomology₀ H := t.hasHomology₀
  have : (t.homology₀ (H := H)).ShiftSequence ℤ := Functor.ShiftSequence.tautological _ _
  obtain ⟨Z, f₂, f₃, h⟩ := distinguished_cocone_triangle (t.ιHeart.map S.f)
  have := t.cocone_heart_isLE_zero (H := H) h
  have : t.IsGE Z 0 := by
    rw [t.isGE_succ_iff_isGE_and_isZero_homology (H := H) Z (-1) 0 (by linarith)]
    constructor
    · exact t.cocone_heart_isGE_neg_one (H := H) h
    · apply (t.homology_exact₃ _ h (-1) 0 (by linarith)).isZero_X₂
      · apply IsZero.eq_of_src
        dsimp
        apply t.isZero_homology_of_isGE _ _ 0 (by linarith)
      · apply (t.homology_exact₁ _ h (-1) 0 (by linarith)).mono_g_iff.1
        have := hS.mono_f
        dsimp
        infer_instance
  have hZ : t.heart Z := by
    rw [mem_heart_iff]
    constructor <;> infer_instance
  let Y := t.heartMk (H := H) _ hZ
  let g' : S.X₂ ⟶ Y := t.ιHeart.preimage (f₂ ≫ (t.ιHeartObjHeartMkIso _ hZ).inv)
  let δ' : t.ιHeart.obj Y ⟶ (t.ιHeart.obj S.X₁)⟦(1 : ℤ)⟧ :=
    (t.ιHeartObjHeartMkIso _ hZ).hom ≫ f₃
  have h' : Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map g') δ' ∈ distTriang C := by
    refine isomorphic_distinguished _ h _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (t.ιHeartObjHeartMkIso _ hZ) ?_ ?_ ?_
    all_goals simp [g', δ']
  obtain ⟨e, he⟩ : ∃ (e : S.X₃ ≅ Y), S.g ≫ e.hom = g' := by
    have h₁ := hS.gIsCokernel
    have h₂ := (t.shortExact_of_distTriang _ h').gIsCokernel
    exact ⟨IsColimit.coconePointUniqueUpToIso h₁ h₂,
      IsColimit.comp_coconePointUniqueUpToIso_hom h₁ h₂ WalkingParallelPair.one⟩
  refine ⟨t.ιHeart.map e.hom ≫ δ', isomorphic_distinguished _ h' _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (t.ιHeart.mapIso e) ?_ ?_ ?_
  · dsimp
    simp
  · dsimp
    simp only [id_comp, ← Functor.map_comp, he]
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

noncomputable def mapHeartShortExactTriangle {S₁ S₂ : ShortComplex H} (φ : S₁ ⟶ S₂)
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

variable {H : Type*} [Category* H] [Abelian H] [t.Heart H] [t.HasHomology₀ H]
  [(t.homology₀ (H := H)).ShiftSequence ℤ]

noncomputable def homologyCompιHeartIso (q : ℤ) :
    t.homology (H := H) q ⋙ t.ιHeart ≅ t.truncGELE q q ⋙ shiftFunctor C q :=
  Functor.isoWhiskerRight ((t.homology₀.shiftIso q 0 q (add_zero q)).symm ≪≫
    Functor.isoWhiskerLeft _ (t.homology₀.isoShiftZero ℤ)) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _  t.homology₀ιHeart ≪≫
    (t.shiftTruncGELE q 0 q 0 q (add_zero q) (add_zero q)).symm

variable (X : C) (q q' : ℤ) (hqq' : q + 1 = q')

noncomputable def shiftSpectralObjectω₁IsoHomologyιHeart :
    ((spectralObject t X).ω₁ ⋙ shiftFunctor C q).obj
        (ComposableArrows.mk₁ (homOfLE (by simp; linarith) : (q : EInt) ⟶ q')) ≅
      (t.homology q ⋙ t.ιHeart (H := H)).obj X :=
  (shiftFunctor C q).mapIso ((t.truncGELEIsoTruncGELT q q q' hqq').symm.app X) ≪≫
    ((t.homologyCompιHeartIso q).app X).symm

end

section

variable {H : Type*} [Category* H] [Abelian H] [t.Heart H] [t.HasHomology₀ H]
  [(t.homology₀ (H := H)).ShiftSequence ℤ]
  (T : Triangle C) (hT : T ∈ distTriang C)

include hT

lemma mono_homologyFunctor_map_mor₂ (n : ℤ) (h : IsZero ((t.homology (H := H) n).obj T.obj₁)) :
    Mono ((t.homology (H := H) n).map T.mor₂) :=
  (t.homology_exact₂ T hT n).mono_g (h.eq_of_src _ _)

lemma epi_homologyFunctor_map_mor₂ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (h : IsZero ((t.homology (H := H) n₁).obj T.obj₁)) :
    Epi ((t.homology (H := H) n₀).map T.mor₂) :=
  (t.homology_exact₃ T hT _ _ hn₁).epi_f (h.eq_of_tgt _ _)

lemma isIso_homologyFunctor_map_mor₂_of_isGE (n : ℤ) (a : ℤ) (h : n + 2 ≤ a)
    (h : t.IsGE T.obj₁ a) :
    IsIso ((t.homology (H := H) n).map T.mor₂) := by
  have := t.mono_homologyFunctor_map_mor₂ T hT n
    (t.isZero_homology_of_isGE (H := H) _ _ a (by omega))
  have := t.epi_homologyFunctor_map_mor₂ T hT n _ rfl
    (t.isZero_homology_of_isGE (H := H) _ _ a (by omega))
  apply isIso_of_mono_of_epi

end

end TStructure

end Triangulated

end CategoryTheory
