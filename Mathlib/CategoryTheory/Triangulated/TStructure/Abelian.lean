import Mathlib.CategoryTheory.Triangulated.TStructure.Trunc
import Mathlib.CategoryTheory.Limits.FullSubcategory

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

namespace Abelian

variable (C : Type*) [Category C] [Preadditive C] [HasFiniteProducts C]
  (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ∃ (K : C) (i : K ⟶ X) (wi : i ≫ f = 0) (_hi : IsLimit (KernelFork.ofι _ wi))
    (Q : C) (p : Y ⟶ Q) (wp : f ≫ p = 0) (_hp : IsColimit (CokernelCofork.ofπ _ wp))
    (I : C) (π : X ⟶ I) (wπ : i ≫ π = 0) (_hπ : IsColimit (CokernelCofork.ofπ _ wπ))
    (ι : I ⟶ Y) (wι : ι ≫ p = 0) (_hι : IsLimit (KernelFork.ofι _ wι)), f = π ≫ ι)

noncomputable def mk' : Abelian C where
  has_kernels := ⟨fun {X Y} f => by
    obtain ⟨K, i, wi, hi, _⟩ := h f
    exact ⟨_, hi⟩⟩
  has_cokernels := ⟨fun {X Y} f => by
    obtain ⟨_, _, _, _, Q, p, wp, hp, _⟩ := h f
    exact ⟨_, hp⟩⟩
  normalMonoOfMono {X Y} f _ := by
    apply Nonempty.some
    obtain ⟨K, i, wi, _, Q, p, wp, _, I, π, wπ, hπ, ι, wι, hι, fac⟩ := h f
    refine'
     ⟨{ Z := Q
        g := p
        w := by rw [fac, assoc, wι, comp_zero]
        isLimit := by
          have : IsIso π := CokernelCofork.IsColimit.isIso_π _ hπ (by
            rw [← cancel_mono f, zero_comp, wi])
          exact IsLimit.ofIsoLimit hι (Fork.ext (by exact asIso π)
            (by exact fac.symm)).symm }⟩
  normalEpiOfEpi {X Y} f _ := by
    apply Nonempty.some
    obtain ⟨K, i, wi, _, Q, p, wp, _, I, π, wπ, hπ, ι, wι, hι, fac⟩ := h f
    refine'
     ⟨{ W := K
        g := i
        w := by rw [fac, reassoc_of% wπ, zero_comp]
        isColimit := by
          have : IsIso ι := KernelFork.IsLimit.isIso_ι _ hι (by
            rw [← cancel_epi f, comp_zero, wp])
          exact IsColimit.ofIsoColimit hπ (Cofork.ext (asIso ι) fac.symm) }⟩

end Abelian

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Set C} (hA : ∀ {X Y : C} {n : ℤ} (f : X ⟶ Y⟦n⟧), X ∈ A → Y ∈ A → n < 0 → f = 0)

namespace Triangulated

open Pretriangulated

variable (T : Triangle C) (hT : T ∈ distTriang C) (hT₁ : T.obj₁ ∈ A) (hT₂ : T.obj₂ ∈ A)
  {K Q : C} (α : K⟦(1 : ℤ)⟧ ⟶ T.obj₃) (β : T.obj₃ ⟶ Q) {γ : Q ⟶ K⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
  (hT' : Triangle.mk α β γ ∈ distTriang C) (hK : K ∈ A) (hQ : Q ∈ A)

namespace AbelianSubcategory

lemma vanishing_from_positive_shift {X Y : C} {n : ℤ} (f : X⟦n⟧ ⟶ Y)
    (hX : X ∈ A) (hY : Y ∈ A) (hn : 0 < n) : f = 0 := by
  apply (shiftFunctor C (-n)).map_injective
  rw [← cancel_epi ((shiftEquiv C n).unitIso.hom.app X), Functor.map_zero, comp_zero]
  exact hA _ hX hY (by linarith)

noncomputable def ιK : K ⟶ T.obj₁ := (shiftFunctor C (1 : ℤ)).preimage (α ≫ T.mor₃)

def πQ : T.obj₂ ⟶ Q := T.mor₂ ≫ β

@[simp, reassoc]
lemma shift_ιK : (ιK T α)⟦(1 : ℤ)⟧' = α ≫ T.mor₃ := by
  simp [ιK]

variable {T}

lemma ιK_mor₁ : ιK T α ≫ T.mor₁ = 0 := by
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simp only [Functor.map_comp, shift_ιK, assoc, Functor.map_zero]
  rw [comp_dist_triangle_mor_zero₃₁ T hT, comp_zero]

lemma mor₂_πQ : T.mor₁ ≫ πQ T β = 0 := by
  dsimp [πQ]
  rw [comp_dist_triangle_mor_zero₁₂_assoc T hT, zero_comp]

variable {α β}

lemma ιK_cancel_zero
    {B : C} (k : B ⟶ K) (hB : B ∈ A) (hk : k ≫ ιK T α = 0) : k = 0 := by
  replace hk := (shiftFunctor C (1 : ℤ)).congr_map hk
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simp only [Functor.map_comp, Functor.map_zero, shift_ιK, ← assoc] at hk ⊢
  obtain ⟨l, hl⟩ := T.coyoneda_exact₃ hT _ hk
  obtain rfl : l = 0 := vanishing_from_positive_shift hA _ hB hT₂ (by linarith)
  rw [zero_comp] at hl
  obtain ⟨m, hm⟩ := Triangle.coyoneda_exact₁ _ hT' (k⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧') (by
    dsimp
    rw [← Functor.map_comp, hl, Functor.map_zero])
  dsimp at m
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by linarith)).hom.app B),
      comp_zero]
    exact vanishing_from_positive_shift hA _ hB hQ (by linarith)
  rw [zero_comp] at hm
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [hm, Functor.map_zero]

lemma πQ_cancel_zero
    {B : C} (k : Q ⟶ B) (hB : B ∈ A) (hk : πQ T β ≫ k = 0) : k = 0 := by
  dsimp [πQ] at hk
  rw [assoc] at hk
  obtain ⟨l, hl⟩ := T.yoneda_exact₃ hT _ hk
  obtain rfl : l = 0 := vanishing_from_positive_shift hA _ hT₁ hB (by linarith)
  rw [comp_zero] at hl
  obtain ⟨m, hm⟩ := Triangle.yoneda_exact₃ _ hT' k hl
  dsimp at m hm
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by linarith)).hom.app K),
      comp_zero]
    exact vanishing_from_positive_shift hA _ hK hB (by linarith)
  rw [hm, comp_zero]

lemma ιK_lift
    {B : C} (x₁ : B ⟶ T.obj₁) (hB : B ∈ A) (hx₁ : x₁ ≫ T.mor₁ = 0) :
    ∃ (k : B ⟶ K), k ≫ ιK T α = x₁ := by
  suffices ∃ (k' : B⟦(1 : ℤ)⟧ ⟶ K⟦(1 : ℤ)⟧), x₁⟦(1 : ℤ)⟧' = k' ≫ α ≫ T.mor₃ by
    obtain ⟨k', hk'⟩ := this
    refine' ⟨(shiftFunctor C (1 : ℤ)).preimage k', _⟩
    apply (shiftFunctor C (1 : ℤ)).map_injective
    rw [Functor.map_comp, Functor.image_preimage, shift_ιK, hk']
  obtain ⟨x₃, hx₃⟩ := T.coyoneda_exact₁ hT (x₁⟦(1 : ℤ)⟧')
    (by rw [← Functor.map_comp, hx₁, Functor.map_zero])
  obtain ⟨k', hk'⟩ := Triangle.coyoneda_exact₂ _ hT' x₃
    (vanishing_from_positive_shift hA _ hB hQ (by linarith))
  refine' ⟨k', _⟩
  dsimp at hk'
  rw [hx₃, hk', assoc]

lemma πQ_desc
    {B : C} (x₂ : T.obj₂ ⟶ B) (hB : B ∈ A) (hx₂ : T.mor₁ ≫ x₂ = 0) :
    ∃ (k : Q ⟶ B), πQ T β ≫ k = x₂ := by
  obtain ⟨x₁, hx₁⟩ := T.yoneda_exact₂ hT x₂ hx₂
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT' x₁
    (vanishing_from_positive_shift hA _ hK hB (by linarith))
  dsimp at k hk
  refine' ⟨k, _⟩
  dsimp [πQ]
  rw [assoc, hx₁, hk]

variable (α β)

noncomputable abbrev kernelFork :=
  @KernelFork.ofι (FullSubcategory A) _ _ ⟨T.obj₁, hT₁⟩ ⟨T.obj₂, hT₂⟩ T.mor₁ ⟨K, hK⟩
    (ιK T α) (ιK_mor₁ hT α)

noncomputable abbrev cokernelFork :=
  @CokernelCofork.ofπ (FullSubcategory A) _ _ ⟨T.obj₁, hT₁⟩ ⟨T.obj₂, hT₂⟩ T.mor₁ ⟨Q, hQ⟩
    (πQ T β) (mor₂_πQ hT β)

variable {α β}

noncomputable def isLimitKernelFork : IsLimit (kernelFork hT hT₁ hT₂ α hK) :=
  KernelFork.IsLimit.ofι _ _ (fun {B} x₁ hx₁ => (ιK_lift hA hT hT' hQ x₁ B.2 hx₁).choose)
    (fun {B} x₁ hx₁ => (ιK_lift hA hT hT' hQ x₁ B.2 hx₁).choose_spec)
    (fun {B} x₁ hx₁ m hm => by
      rw [← sub_eq_zero]
      refine' ιK_cancel_zero hA hT hT₂ hT' hQ _ B.2 _
      rw [sub_comp, sub_eq_zero, (ιK_lift hA hT hT' hQ x₁ B.2 hx₁).choose_spec]
      exact hm)

noncomputable def isColimitCokernelCofork : IsColimit (cokernelFork hT hT₁ hT₂ β hQ) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {B} x₂ hx₂ => (πQ_desc hA hT hT' hK x₂ B.2 hx₂).choose)
    (fun {B} x₂ hx₂ => (πQ_desc hA hT hT' hK x₂ B.2 hx₂).choose_spec)
    (fun {B} x₂ hx₂ m hm => by
      rw [← sub_eq_zero]
      refine' πQ_cancel_zero hA hT hT₁ hT' hK _ B.2 _
      rw [comp_sub, sub_eq_zero, (πQ_desc hA hT hT' hK x₂ B.2 hx₂).choose_spec]
      exact hm)

-- BBD 1.2.1, p. 27
lemma hasKernel :
    HasKernel (show FullSubcategory.mk T.obj₁ hT₁ ⟶ FullSubcategory.mk T.obj₂ hT₂ from T.mor₁) :=
  ⟨_, isLimitKernelFork hA hT hT₁ hT₂ hT' hK hQ⟩

lemma hasCokernel :
    HasCokernel (show FullSubcategory.mk T.obj₁ hT₁ ⟶ FullSubcategory.mk T.obj₂ hT₂ from T.mor₁) :=
  ⟨_, isColimitCokernelCofork hA hT hT₁ hT₂ hT' hK hQ⟩

end AbelianSubcategory

variable (t : TStructure C) [IsTriangulated C]

namespace TStructure

variable {T : Triangle C} (hT : T ∈ distTriang C)
  (hT₁ : T.obj₁ ∈ t.heart) (hT₂ : T.obj₂ ∈ t.heart)

lemma cocone_heart_isLE_zero : t.IsLE T.obj₃ 0 := by
  have : t.IsLE T.obj₁ 0 := ⟨hT₁.1⟩
  have : t.IsLE T.obj₁ 1 := t.isLE_of_LE T.obj₁ 0 1 (by linarith)
  exact t.isLE₂ _ (rot_of_dist_triangle _ hT) 0 ⟨hT₂.1⟩
    (t.isLE_shift T.obj₁ 1 1 0 (add_zero 1))

lemma cocone_heart_isGE_neg_one : t.IsGE T.obj₃ (-1) := by
  have : t.IsGE T.obj₁ 0 := ⟨hT₁.2⟩
  have : t.IsGE T.obj₂ 0 := ⟨hT₂.2⟩
  exact t.isGE₂ _ (rot_of_dist_triangle _ hT) (-1)
    (t.isGE_of_GE T.obj₂ (-1) 0 (by linarith))
    (t.isGE_shift T.obj₁ 0 1 (-1) (by linarith))

section

variable (X : C) [t.IsLE X 0] [t.IsGE X (-1)]

namespace TriangleOfGENegOneOfLEZero

noncomputable def truncLTZeroIso :
  (t.truncLT 0).obj X ≅
    (t.homology' (-1) ⋙ t.ιHeartDegree (-1)).obj X :=
  (t.truncLEIsoTruncLT (-1) 0 (by linarith)).symm.app X ≪≫
    asIso ((t.truncGEπ (-1)).app ((t.truncLE (-1)).obj X)) ≪≫
    (t.homologyCompιHeartDegreeIsoHomology' (-1)).symm.app X

noncomputable def truncGEZeroIso : (t.truncGE 0).obj X ≅ (t.homology' 0 ⋙ t.ιHeart').obj X :=
  (t.truncGE 0).mapIso (asIso ((t.truncLEι 0).app X)).symm ≪≫
    (shiftFunctorZero C ℤ).symm.app _

@[simps]
noncomputable def triangle : Triangle C where
  obj₁ := (t.homology' (-1) ⋙ t.ιHeartDegree (-1)).obj X
  obj₂ := X
  obj₃ := (t.homology' 0 ⋙ t.ιHeart').obj X
  mor₁ := (truncLTZeroIso t X).inv ≫ (t.truncLTι 0).app X
  mor₂ := (t.truncGEπ 0).app X ≫ (truncGEZeroIso t X).hom
  mor₃ := (truncGEZeroIso t X).inv ≫ (t.truncGEδLT 0).app X ≫
    (truncLTZeroIso t X).hom⟦(1 : ℤ)⟧'

noncomputable def triangleIso :
    triangle t X ≅ (t.triangleLTGE 0).obj X := by
  refine' Triangle.isoMk _ _ (truncLTZeroIso t X).symm (Iso.refl _)
    (truncGEZeroIso t X).symm _ _ _
  · dsimp
    aesop_cat
  · dsimp
    simp
  · dsimp
    simp only [assoc, Iso.cancel_iso_inv_left, ← Functor.map_comp, Iso.hom_inv_id,
      Functor.map_id, comp_id]

lemma triangle_distinguished :
    triangle t X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLTGE_distinguished 0 X) _
    (triangleIso t X)

end TriangleOfGENegOneOfLEZero

end

namespace Heart

lemma vanishing_to_negative_shift {X Y : C} {n : ℤ} (f : X ⟶ Y⟦n⟧)
    (hX : X ∈ t.heart) (hY : Y ∈ t.heart) (hn : n < 0) : f = 0 := by
  rw [t.mem_heart_iff] at hX hY
  have : t.IsLE X 0 := hX.1
  have := hY.2
  have : t.IsGE (Y⟦n⟧) (-n) := t.isGE_shift Y 0 n (-n) (by linarith)
  exact t.zero f 0 (-n) (by linarith)

instance : HasKernels t.Heart' where
  has_limit {X₁ X₂} f₁ := by
    obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (t.ιHeart'.map f₁)
    have : t.IsLE X₃ 0 := cocone_heart_isLE_zero t hT X₁.2 X₂.2
    have : t.IsGE X₃ (-1) := cocone_heart_isGE_neg_one t hT X₁.2 X₂.2
    exact AbelianSubcategory.hasKernel (vanishing_to_negative_shift t) hT X₁.2 X₂.2
      (TriangleOfGENegOneOfLEZero.triangle_distinguished t X₃) (t.ιHeart_obj_mem_heart _)
        (t.ιHeart_obj_mem_heart ((t.homology' 0).obj X₃))

instance : HasCokernels t.Heart' where
  has_colimit {X₁ X₂} f₁ := by
    obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (t.ιHeart'.map f₁)
    have : t.IsLE X₃ 0 := cocone_heart_isLE_zero t hT X₁.2 X₂.2
    have : t.IsGE X₃ (-1) := cocone_heart_isGE_neg_one t hT X₁.2 X₂.2
    exact AbelianSubcategory.hasCokernel (vanishing_to_negative_shift t) hT X₁.2 X₂.2
      (TriangleOfGENegOneOfLEZero.triangle_distinguished t X₃) (t.ιHeart_obj_mem_heart _)
        (t.ιHeart_obj_mem_heart ((t.homology' 0).obj X₃))

noncomputable def isLimitKernelForkOfDistTriang {X₁ X₂ X₃ : t.Heart'}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃.1 ⟶ X₁.1⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (t.ιHeart'.map f) (t.ιHeart'.map g) h ∈ distTriang C) :
    IsLimit (KernelFork.ofι f (show f ≫ g = 0 from comp_dist_triangle_mor_zero₁₂ _ hT)) := by
  refine' IsLimit.ofIsoLimit (AbelianSubcategory.isLimitKernelFork (vanishing_to_negative_shift t)
    (rot_of_dist_triangle _ hT) _ _ (contractible_distinguished (X₁.1⟦(1 : ℤ)⟧)) X₁.2 (by
      rw [mem_heart_iff]
      constructor <;> infer_instance)) _
  exact Fork.ext (mulIso (-1) (Iso.refl _))
    ((shiftFunctor C (1 : ℤ)).map_injective (by aesop_cat))

noncomputable def isColimitCokernelCoforkOfDistTriang {X₁ X₂ X₃ : t.Heart'}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃.1 ⟶ X₁.1⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (t.ιHeart'.map f) (t.ιHeart'.map g) h ∈ distTriang C) :
    IsColimit (CokernelCofork.ofπ g (show f ≫ g = 0 from comp_dist_triangle_mor_zero₁₂ _ hT)) := by
  have hT' : Triangle.mk (0 : (0 : C)⟦(1 : ℤ)⟧ ⟶ _) (𝟙 X₃.1) 0 ∈ distTriang C := by
    refine' isomorphic_distinguished _ (inv_rot_of_dist_triangle _ (contractible_distinguished X₃.1)) _ _
    refine' Triangle.isoMk _ _ (IsZero.iso _ _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
    all_goals
      dsimp
      rw [IsZero.iff_id_eq_zero, ← Functor.map_id, id_zero, Functor.map_zero]
  refine' IsColimit.ofIsoColimit (AbelianSubcategory.isColimitCokernelCofork (vanishing_to_negative_shift t)
    hT X₁.2 X₂.2 hT' (by
      rw [mem_heart_iff]
      constructor <;> infer_instance) X₃.2) _
  exact Cofork.ext (Iso.refl _) (by simp [AbelianSubcategory.πQ])

instance : HasTerminal t.Heart' := by
  let Z : t.Heart' := ⟨0, by
    change 0 ∈ t.heart
    rw [t.mem_heart_iff]
    constructor <;> infer_instance⟩
  have : ∀ (X : t.Heart'), Inhabited (X ⟶ Z) := fun X => ⟨0⟩
  have : ∀ (X : t.Heart'), Unique (X ⟶ Z) := fun X =>
    { uniq := fun f => t.ιHeart'.map_injective ((isZero_zero C).eq_of_tgt _ _) }
  exact hasTerminal_of_unique Z

lemma prod_mem (X₁ X₂ : C) (hX₁ : X₁ ∈ t.heart) (hX₂ : X₂ ∈ t.heart) :
    (X₁ ⨯ X₂) ∈ t.heart := by
  rw [t.mem_heart_iff]
  constructor
  · exact t.isLE₂ _ (binaryProductTriangle_distinguished X₁ X₂) 0 ⟨hX₁.1⟩ ⟨hX₂.1⟩
  · exact t.isGE₂ _ (binaryProductTriangle_distinguished X₁ X₂) 0 ⟨hX₁.2⟩ ⟨hX₂.2⟩

instance : HasBinaryProducts t.Heart' := by
  apply hasLimitsOfShape_of_closed_under_limits
  intro F c hc H
  exact t.heart.mem_of_iso
    (limit.isoLimitCone ⟨_, (IsLimit.postcomposeHomEquiv (diagramIsoPair F) _).symm hc⟩)
    (prod_mem t _ _ (H _) (H _))

instance : HasFiniteProducts t.Heart' := hasFiniteProducts_of_has_binary_and_terminal

noncomputable instance : Abelian t.Heart' := by
  apply Abelian.mk'
  intro X₁ X₂ f₁
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (t.ιHeart'.map f₁)
  have : t.IsLE X₃ 0 := cocone_heart_isLE_zero t hT X₁.2 X₂.2
  have : t.IsGE X₃ (-1) := cocone_heart_isGE_neg_one t hT X₁.2 X₂.2
  let K := (t.homology' (-1)).obj X₃
  have hK := AbelianSubcategory.isLimitKernelFork (vanishing_to_negative_shift t) hT X₁.2 X₂.2
    (TriangleOfGENegOneOfLEZero.triangle_distinguished t X₃) (t.ιHeart_obj_mem_heart _)
      (t.ιHeart_obj_mem_heart ((t.homology' 0).obj X₃))
  let Q := (t.homology' 0).obj X₃
  have hQ := AbelianSubcategory.isColimitCokernelCofork (vanishing_to_negative_shift t) hT X₁.2 X₂.2
    (TriangleOfGENegOneOfLEZero.triangle_distinguished t X₃) (t.ιHeart_obj_mem_heart _)
      (t.ιHeart_obj_mem_heart ((t.homology' 0).obj X₃))
  dsimp
  let a : (t.ιHeart'.obj K)⟦(1 : ℤ)⟧ ⟶ X₃ := (TriangleOfGENegOneOfLEZero.triangle t X₃).mor₁
  let b := (TriangleOfGENegOneOfLEZero.triangle t X₃).mor₂
  let i : K ⟶ X₁ := AbelianSubcategory.ιK (Triangle.mk (t.ιHeart'.map f₁) f₂ f₃) a
  let p : X₂ ⟶ Q := AbelianSubcategory.πQ (Triangle.mk (t.ιHeart'.map f₁) f₂ f₃) b
  have comm : a ≫ f₃ = a ≫ f₃ := rfl
  obtain ⟨I₀, π, g, hI⟩ := distinguished_cocone_triangle (t.ιHeart'.map i)
  let T₃ := (Triangle.mk (t.ιHeart'.map i) π g)⟦(1 : ℤ)⟧
  let T'₃ := Triangle.mk (a ≫ f₃) T₃.mor₂ (-T₃.mor₃)
  have h₁ := (TriangleOfGENegOneOfLEZero.triangle_distinguished t X₃)
  have h₂ := rot_of_dist_triangle _ (rot_of_dist_triangle _ hT)
  have h₃ : T'₃ ∈ distTriang C := by
    refine' isomorphic_distinguished _ (Triangle.shift_distinguished _ hI 1) _ _
    refine' Triangle.isoMk _ _ (mulIso (-1) (Iso.refl _)) (Iso.refl _) (Iso.refl _) _ _ _
    all_goals dsimp; simp
  have H := someOctahedron comm h₁ h₂ h₃
  let I : t.Heart' := ⟨I₀, by
    change I₀ ∈ t.heart
    rw [t.mem_heart_iff]
    constructor
    · have : t.IsLE ((t.homology' (-1)).obj X₃).1 1 := t.isLE_of_LE _ 0 1 (by linarith)
      exact t.isLE₂ _ (rot_of_dist_triangle _ hI) 0 ⟨X₁.2.1⟩
        (t.isLE_shift ((t.homology' (-1)).obj X₃).1 1 1 0 (add_zero 1))
    · suffices t.IsGE (I₀⟦(1 : ℤ)⟧) (-1) by
        have := t.isGE_shift (I₀⟦(1 : ℤ)⟧) (-1) (-1) 0 (add_zero (-1))
        have e := (shiftEquiv C (1 : ℤ)).unitIso.symm.app I₀
        dsimp at e
        exact t.isGE_of_iso e 0
      apply t.isGE₂ _ H.mem (-1)
      · dsimp
        exact t.isGE_of_GE _ (-1) 0 (by linarith)
      · exact t.isGE_shift X₂.1 0 1 (-1) (by linarith)⟩
  let π' : X₁ ⟶ I := π
  let ι : I₀ ⟶ X₂.1 := (shiftFunctor C (1 : ℤ)).preimage H.m₃
  let ι' : I ⟶ X₂ := ι
  have hι' : f₁ = π' ≫ ι' := by
    apply t.ιHeart'.map_injective
    apply (shiftFunctor C (1 : ℤ)).map_injective
    have eq := H.comm₃
    dsimp at eq
    simp only [neg_smul, one_smul, neg_comp, neg_inj] at eq
    refine' eq.symm.trans _
    simp only [Functor.map_comp]
    dsimp
    simp only [Functor.image_preimage]
  have mem : Triangle.mk ι (t.ιHeart'.map p) (-H.m₁) ∈ distTriang C := by
    rw [← Triangle.shift_distinguished_iff _ 1]
    refine' isomorphic_distinguished _ (rot_of_dist_triangle _ H.mem) _ _
    refine' Triangle.isoMk _ _ (mulIso (-1) (Iso.refl _)) (Iso.refl _) (Iso.refl _) _ _ _
    · dsimp
      simp
    · dsimp [AbelianSubcategory.πQ]
      simp
    · dsimp
      simp
  exact ⟨K, i, _, hK, Q, p, _, hQ, I, π', _, isColimitCokernelCoforkOfDistTriang t i π' _ hI,
    ι', _, isLimitKernelForkOfDistTriang t ι' p _ mem, hι'⟩

end Heart

end TStructure

end Triangulated

end CategoryTheory
