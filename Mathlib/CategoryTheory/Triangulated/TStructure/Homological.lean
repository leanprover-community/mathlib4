import Mathlib.CategoryTheory.Triangulated.TStructure.Abelian
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab

open CategoryTheory Category Limits Pretriangulated Preadditive

lemma AddCommGroupCat.isZero (X : AddCommGroupCat) (hX : ∀ (x : X), x = 0) :
    Limits.IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  ext x
  exact hX x

namespace CategoryTheory

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

namespace Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (t : TStructure C)

namespace TStructure

section

instance (n : ℤ) (X : C) [t.IsLE X n] : t.IsLE ((shiftFunctor C (1 : ℤ)).obj X) n := by
  have : t.IsLE (((shiftFunctor C (1 : ℤ))).obj X) (n-1) :=
    t.isLE_shift X n 1 (n-1) (by linarith)
  exact t.isLE_of_LE _ (n-1) n (by linarith)

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

noncomputable def toHomology₀ (X : C) [t.IsLE X 0] : X ⟶ t.ιHeart'.obj ((t.homology' 0).obj X) :=
  (asIso ((t.truncLEι 0).app X)).inv ≫ (t.truncGEπ 0).app _ ≫ (shiftFunctorZero C ℤ).inv.app _

@[reassoc]
lemma truncLEι_toHomology₀_shiftFunctorZero_hom (X : C) [t.IsLE X 0] :
    (t.truncLEι 0).app X ≫ t.toHomology₀ X ≫ (shiftFunctorZero C ℤ).hom.app _ =
      (t.truncGEπ 0).app _ := by
  dsimp only [toHomology₀]
  rw [assoc, assoc]
  erw [Iso.inv_hom_id_app, comp_id]
  rw [asIso_inv, IsIso.hom_inv_id_assoc]

lemma toHomology₀_naturality {X Y : C} (f : X ⟶ Y) [t.IsLE X 0] [t.IsLE Y 0] :
    t.toHomology₀ X ≫ (t.homology' 0 ⋙ t.ιHeart').map f = f ≫ t.toHomology₀ Y := by
  rw [← cancel_mono ((shiftFunctorZero C ℤ).hom.app _), assoc, assoc,
    ← cancel_epi ((t.truncLEι 0).app X)]
  erw [← (t.truncLEι 0).naturality_assoc f]
  rw [t.truncLEι_toHomology₀_shiftFunctorZero_hom Y]
  erw [(shiftFunctorZero C ℤ).hom.naturality]
  rw [t.truncLEι_toHomology₀_shiftFunctorZero_hom_assoc X]
  erw [(t.truncGEπ 0).naturality]
  rfl

instance (X : C) : t.IsLE ((t.truncLT 0).obj X) (-1) :=
  t.isLE_of_iso ((t.truncLEIsoTruncLT (-1) 0 (by linarith)).app X) (-1)

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

noncomputable def fromHomology₀ (X : C) [t.IsGE X 0] : t.ιHeart'.obj ((t.homology' 0).obj X) ⟶ X :=
  t.homology₀CompιHeartIsoTruncLEGE.hom.app X ≫ (t.truncLEι 0).app _ ≫ (asIso ((t.truncGEπ 0).app X)).inv

@[reassoc]
lemma homology₀CompιHeartIsoTruncLEGE_inv_app_fromHomology₀_truncGEπ (X : C) [t.IsGE X 0] :
    t.homology₀CompιHeartIsoTruncLEGE.inv.app X ≫ t.fromHomology₀ X ≫ (t.truncGEπ 0).app X =
      (t.truncLEι 0).app ((t.truncGE 0).obj X) := by
  simp [fromHomology₀]

lemma fromHomology₀_naturality {X Y : C} (f : X ⟶ Y) [t.IsGE X 0] [t.IsGE Y 0] :
    (t.homology' 0 ⋙ t.ιHeart').map f ≫ t.fromHomology₀ Y = t.fromHomology₀ X ≫ f := by
  rw [← cancel_mono ((t.truncGEπ 0).app Y), assoc, assoc]
  erw [(t.truncGEπ 0).naturality f]
  rw [← cancel_epi (t.homology₀CompιHeartIsoTruncLEGE.inv.app X),
    homology₀CompιHeartIsoTruncLEGE_inv_app_fromHomology₀_truncGEπ_assoc,
    ← NatTrans.naturality_assoc,
    homology₀CompιHeartIsoTruncLEGE_inv_app_fromHomology₀_truncGEπ]
  dsimp [truncLEGE]
  apply NatTrans.naturality

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
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

namespace HomologicalFunctorAux

variable {T : Triangle C} (hT : T ∈ distTriang C)

instance : (t.homology' 0).Additive where
  map_add {X Y f g} := by
    apply t.ιHeart'.map_injective
    simp [homology']

@[simps!]
noncomputable def shortComplex :=
  (ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).map (t.homology' 0)

lemma case₁ [t.IsLE T.obj₁ 0] [t.IsLE T.obj₂ 0] [t.IsLE T.obj₃ 0] :
    (shortComplex t hT).Exact ∧ Epi (shortComplex t hT).g := by
  let S := fun A => (shortComplex t hT).op.map (preadditiveYoneda.obj A)
  let S' := fun A => (ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).op.map (preadditiveYoneda.obj A)
  suffices ∀ A, (S A).Exact ∧ Mono (S A).f by
    simpa only [ShortComplex.exact_and_epi_g_iff_preadditiveYoneda] using this
  intro A
  let e' : ∀ (X : C) [t.IsLE X 0],
    (preadditiveYoneda.obj A).obj (Opposite.op ((t.homology' 0).obj X)) ≅ (preadditiveYoneda.obj A.1).obj (Opposite.op X) :=
      fun X _ => asIso ((preadditiveYoneda.obj A.1).map (t.toHomology₀ X).op)
  have e : S A ≅ S' A.1 := by
    refine' ShortComplex.isoMk (e' T.obj₃) (e' T.obj₂) (e' T.obj₁) _ _
    · simpa only [op_comp, Functor.map_comp] using (preadditiveYoneda.obj A.1).congr_map
        (congr_arg Quiver.Hom.op (t.toHomology₀_naturality T.mor₂).symm)
    · simpa only [op_comp, Functor.map_comp] using (preadditiveYoneda.obj A.1).congr_map
        (congr_arg Quiver.Hom.op (t.toHomology₀_naturality T.mor₁).symm)
  rw [ShortComplex.exact_and_mono_f_iff_of_iso e]
  refine' ⟨preadditiveYoneda_map_distinguished A.1 _ hT,
    (preadditiveYoneda_map_distinguished A.1 _ (rot_of_dist_triangle _ hT)).mono_g _⟩
  apply IsZero.eq_of_src
  apply AddCommGroupCat.isZero
  intro (x : T.obj₁⟦(1 : ℤ)⟧ ⟶ A.obj)
  have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) := t.isLE_shift T.obj₁ 0 1 (-1) (by linarith)
  exact t.zero x (-1) 0 (by linarith)

instance (X : C) (n : ℤ) : IsIso ((t.truncGELE n n).map ((t.truncLEι n).app X)) := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (n : ℤ) : IsIso ((t.homology' n).map ((t.truncLEι n).app X)) := by
  suffices IsIso (t.ιHeart'.map ((t.homology' n).map ((t.truncLEι n).app X))) from
    isIso_of_reflects_iso ((t.homology' n).map ((t.truncLEι n).app X)) t.ιHeart'
  dsimp [homology']
  infer_instance

lemma case₂ (h₁ : t.IsLE T.obj₁ 0) :
    (shortComplex t hT).Exact ∧ Epi (shortComplex t hT).g := by
  have h' := case₁ t (t.truncLETriangle_distinguished T hT 0)
  refine' (ShortComplex.exact_and_epi_g_iff_of_iso _).1 h'
  refine' ShortComplex.isoMk
    (asIso ((t.homology' 0).map ((t.truncLEι 0).app T.obj₁)))
    (asIso ((t.homology' 0).map ((t.truncLEι 0).app T.obj₂)))
    (asIso ((t.homology' 0).map ((t.truncLEι 0).app T.obj₃))) _ _
  all_goals
    dsimp
    simp only [← Functor.map_comp, NatTrans.naturality, Functor.id_obj, Functor.id_map]

lemma case₁' [t.IsGE T.obj₁ 0] [t.IsGE T.obj₂ 0] [t.IsGE T.obj₃ 0] :
    (shortComplex t hT).Exact ∧ Mono (shortComplex t hT).f := by
  let S := fun A => (shortComplex t hT).map (preadditiveCoyoneda.obj (Opposite.op A))
  let S' := fun A => (ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).map (preadditiveCoyoneda.obj (Opposite.op A))
  suffices ∀ A, (S A).Exact ∧ Mono (S A).f by
    rw [ShortComplex.exact_and_mono_f_iff_preadditiveCoyoneda]
    exact this
  intro A
  let e' : ∀ (X : C) [t.IsGE X 0],
    (preadditiveCoyoneda.obj (Opposite.op A)).obj (((t.homology' 0).obj X)) ≅
    (preadditiveCoyoneda.obj (Opposite.op A.1)).obj X := fun X _ =>
      asIso ((preadditiveCoyoneda.obj (Opposite.op A.1)).map (t.fromHomology₀ X))
  have e : S A ≅ S' A.1 := by
    refine' ShortComplex.isoMk (e' T.obj₁) (e' T.obj₂) (e' T.obj₃) _ _
    · simpa only [Functor.map_comp] using
        (preadditiveCoyoneda.obj (Opposite.op A.1)).congr_map (t.fromHomology₀_naturality T.mor₁).symm
    · simpa only [Functor.map_comp] using
        (preadditiveCoyoneda.obj (Opposite.op A.1)).congr_map (t.fromHomology₀_naturality T.mor₂).symm
  rw [ShortComplex.exact_and_mono_f_iff_of_iso e]
  refine' ⟨(preadditiveCoyoneda.obj (Opposite.op A.1)).map_distinguished_exact _ hT,
    ((preadditiveCoyoneda.obj (Opposite.op A.1)).map_distinguished_exact _ (inv_rot_of_dist_triangle _ hT)).mono_g _⟩
  apply IsZero.eq_of_src
  apply AddCommGroupCat.isZero
  intro (x : A.obj ⟶ T.obj₃⟦-1⟧)
  have : t.IsGE (T.obj₃⟦(-1 : ℤ)⟧) 1 := t.isGE_shift T.obj₃ 0 (-1) 1 (by linarith)
  exact t.zero x 0 1 (by linarith)

instance (X : C) (n : ℤ) : IsIso ((t.truncGE n).map ((t.truncGEπ n).app X)) := by
  apply isIso_truncGE_map_truncGEπ_app
  rfl

instance (X : C) (n : ℤ) : IsIso ((t.truncLTGE n (n+1)).map ((t.truncGEπ n).app X)) := by
  dsimp [truncLTGE]
  infer_instance

instance (X : C) (n : ℤ) : IsIso ((t.truncGELE n n).map ((t.truncGEπ n).app X)) := by
  have e : t.truncGELE n n ≅ t.truncLTGE n (n+1) := asIso (t.natTransTruncGELTTruncLTGE n (n+1))
  rw [NatIso.isIso_map_iff e ((t.truncGEπ n).app X)]
  infer_instance

instance (X : C) (n : ℤ) : IsIso ((t.homology' n).map ((t.truncGEπ n).app X)) := by
  suffices IsIso (t.ιHeart'.map ((t.homology' n).map ((t.truncGEπ n).app X))) from
    isIso_of_reflects_iso ((t.homology' n).map ((t.truncGEπ n).app X)) t.ιHeart'
  dsimp [homology']
  infer_instance

lemma case₂' (h₃ : t.IsGE T.obj₃ 0) :
    (shortComplex t hT).Exact ∧ Mono (shortComplex t hT).f := by
  have h' := case₁' t (t.truncGETriangle_distinguished T hT 0)
  refine' (ShortComplex.exact_and_mono_f_iff_of_iso _).2 h'
  refine' ShortComplex.isoMk
    (asIso ((t.homology' 0).map ((t.truncGEπ 0).app T.obj₁)))
    (asIso ((t.homology' 0).map ((t.truncGEπ 0).app T.obj₂)))
    (asIso ((t.homology' 0).map ((t.truncGEπ 0).app T.obj₃))) _ _
  all_goals
    dsimp
    simp only [← Functor.map_comp]
    congr 1
    exact ((t.truncGEπ 0).naturality _).symm

end HomologicalFunctorAux

instance (X : C) (n : ℤ) : t.IsGE (((t.truncGE n).obj X)⟦n⟧) 0 :=
  t.isGE_shift _ n n 0 (add_zero n)

open HomologicalFunctorAux in
instance : (t.homology' 0).IsHomological where
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
        ((t.homology' 0).map T.mor₂) (by
          dsimp [shortComplex, ShortComplex.map]
          rw [id_comp, ← Functor.map_comp, H.comm₃]) ex₁.1 ex₂.1
    refine' ShortComplex.exact_of_iso _ ex₃.exact₂
    refine' ShortComplex.isoMk (asIso ((t.homology' 0).map ((t.truncLEι 0).app T.obj₁)))
        (Iso.refl _) (Iso.refl _) _ _
    all_goals
      dsimp; simp; rfl

end TStructure

end Triangulated

end CategoryTheory
