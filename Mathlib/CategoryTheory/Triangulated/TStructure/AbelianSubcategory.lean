import Mathlib.CategoryTheory.Triangulated.TStructure.Trunc
import Mathlib.CategoryTheory.Abelian.Constructor
import Mathlib.CategoryTheory.Shift.SingleFunctors

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated ZeroObject

namespace Triangulated

variable {C A : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace AbelianSubcategory

variable [Category A] [Preadditive A] {ι : A ⥤ C} [ι.Additive] [Full ι] [Faithful ι]
  (hι : ∀ ⦃X Y : A⦄ ⦃n : ℤ⦄ (f : ι.obj X ⟶ (ι.obj Y)⟦n⟧), n < 0 → f = 0)

lemma vanishing_from_positive_shift {X Y : A} {n : ℤ} (f : (ι.obj X)⟦n⟧ ⟶ ι.obj Y)
    (hn : 0 < n) : f = 0 := by
  apply (shiftFunctor C (-n)).map_injective
  rw [← cancel_epi ((shiftEquiv C n).unitIso.hom.app _), Functor.map_zero, comp_zero]
  exact hι _ (by linarith)

section

variable {X₁ X₂ : A} {f₁ : X₁ ⟶ X₂} {X₃ : C} (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
  (hT : Triangle.mk (ι.map f₁) f₂ f₃ ∈ distTriang C) {K Q : A}
  (α : (ι.obj K)⟦(1 : ℤ)⟧ ⟶ X₃) (β : X₃ ⟶ (ι.obj Q)) {γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
  (hT' : Triangle.mk α β γ ∈ distTriang C)

noncomputable def ιK : K ⟶ X₁ := (ι ⋙ shiftFunctor C (1 : ℤ)).preimage (α ≫ f₃)

def πQ : X₂ ⟶ Q := ι.preimage (f₂ ≫ β)

@[simp, reassoc]
lemma shift_ι_map_ιK : (ι.map (ιK f₃ α))⟦(1 : ℤ)⟧' = α ≫ f₃ := by
  apply (ι ⋙ shiftFunctor C (1 : ℤ)).image_preimage

@[simp, reassoc]
lemma ι_map_πQ : ι.map (πQ f₂ β) = f₂ ≫ β := by
  apply ι.image_preimage

variable {f₂ f₃}

lemma ιK_mor₁ : ιK f₃ α ≫ f₁ = 0 := by
  apply (ι ⋙ shiftFunctor C (1 : ℤ)).map_injective
  simp only [Functor.comp_map, Functor.map_comp, shift_ι_map_ιK,
    assoc, Functor.map_zero]
  erw [comp_dist_triangle_mor_zero₃₁ _ hT, comp_zero]

lemma mor₁_πQ : f₁ ≫ πQ f₂ β = 0 := by
  apply ι.map_injective
  simp only [Functor.map_comp, Functor.map_zero, ι_map_πQ]
  erw [comp_dist_triangle_mor_zero₁₂_assoc _ hT, zero_comp]

variable {α β}

lemma mono_ιK : Mono (ιK f₃ α) := by
  rw [mono_iff_cancel_zero]
  intro B k hk
  replace hk := (ι ⋙ shiftFunctor C (1 : ℤ)).congr_map hk
  apply (ι ⋙ shiftFunctor C (1 : ℤ)).map_injective
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    shift_ι_map_ιK, Functor.map_zero, ← assoc] at hk ⊢
  obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₃ _ hT _ hk
  obtain rfl : l = 0 := vanishing_from_positive_shift hι _ (by linarith)
  rw [zero_comp] at hl
  obtain ⟨m, hm⟩ := Triangle.coyoneda_exact₁ _ hT' ((ι.map k)⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧') (by
    dsimp
    rw [← Functor.map_comp, hl, Functor.map_zero])
  dsimp at m hm
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by linarith)).hom.app _), comp_zero]
    exact vanishing_from_positive_shift hι _ (by linarith)
  rw [zero_comp] at hm
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [hm, Functor.map_zero]

lemma epi_πQ : Epi (πQ f₂ β) := by
  rw [epi_iff_cancel_zero]
  intro B k hk
  replace hk := ι.congr_map hk
  simp only [Functor.map_comp, ι_map_πQ, assoc, Functor.map_zero] at hk
  obtain ⟨l, hl⟩ := Triangle.yoneda_exact₃ _ hT _ hk
  obtain rfl : l = 0 := vanishing_from_positive_shift hι _ (by linarith)
  rw [comp_zero] at hl
  obtain ⟨m, hm⟩ := Triangle.yoneda_exact₃ _ hT' (ι.map k) hl
  dsimp at m hm
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by linarith)).hom.app _),
      comp_zero]
    exact vanishing_from_positive_shift hι _ (by linarith)
  apply ι.map_injective
  rw [hm, comp_zero, ι.map_zero]

lemma ιK_lift {B : A} (x₁ : B ⟶ X₁) (hx₁ : x₁ ≫ f₁ = 0) :
    ∃ (k : B ⟶ K), k ≫ ιK f₃ α = x₁ := by
  suffices ∃ (k' : (ι.obj B)⟦(1 : ℤ)⟧ ⟶ (ι.obj K)⟦(1 : ℤ)⟧), (ι.map x₁)⟦(1 : ℤ)⟧' = k' ≫ α ≫ f₃ by
    obtain ⟨k', hk'⟩ := this
    refine' ⟨(ι ⋙ shiftFunctor C (1 : ℤ)).preimage k', _⟩
    apply (ι ⋙ shiftFunctor C (1 : ℤ)).map_injective
    rw [Functor.map_comp, Functor.image_preimage, Functor.comp_map, shift_ι_map_ιK,
      Functor.comp_map, hk']
  obtain ⟨x₃, hx₃⟩ := Triangle.coyoneda_exact₁ _ hT ((ι.map x₁)⟦(1 : ℤ)⟧')
    (by
      dsimp
      rw [← Functor.map_comp, ← Functor.map_comp, hx₁, Functor.map_zero, Functor.map_zero])
  obtain ⟨k', hk'⟩ := Triangle.coyoneda_exact₂ _ hT' x₃
    (vanishing_from_positive_shift hι _ (by linarith))
  refine' ⟨k', _⟩
  dsimp at hk' hx₃
  rw [hx₃, hk', assoc]

noncomputable def isLimitKernelFork : IsLimit (KernelFork.ofι _ (ιK_mor₁ hT α)) :=
  KernelFork.IsLimit.ofι _ _  (fun {B} x₁ hx₁ => (ιK_lift hι hT hT' x₁ hx₁).choose)
    (fun {B} x₁ hx₁ => (ιK_lift hι hT hT' x₁ hx₁).choose_spec)
    (fun {B} x₁ hx₁ m hm => by
      have := mono_ιK hι hT hT'
      rw [← cancel_mono (ιK f₃ α), (ιK_lift hι hT hT' x₁ hx₁).choose_spec, hm])

lemma πQ_desc {B : A} (x₂ : X₂ ⟶ B) (hx₂ : f₁ ≫ x₂ = 0) :
    ∃ (k : Q ⟶ B), πQ f₂ β ≫ k = x₂ := by
  obtain ⟨x₁, hx₁⟩ := Triangle.yoneda_exact₂ _ hT (ι.map x₂) (by
    dsimp
    rw [← ι.map_comp, hx₂, ι.map_zero])
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT' x₁
    (vanishing_from_positive_shift hι _ (by linarith))
  dsimp at k hk hx₁
  refine' ⟨ι.preimage k, _⟩
  apply ι.map_injective
  simp only [Functor.map_comp, ι_map_πQ, Functor.image_preimage, assoc, hx₁, hk]

noncomputable def isColimitCokernelCofork : IsColimit (CokernelCofork.ofπ _ (mor₁_πQ hT β)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {B} x₂ hx₂ => (πQ_desc hι hT hT' x₂ hx₂).choose)
    (fun {B} x₂ hx₂ => (πQ_desc hι hT hT' x₂ hx₂).choose_spec)
    (fun {B} x₂ hx₂ m hm => by
      have := epi_πQ hι hT hT'
      rw [← cancel_epi (πQ f₂ β), (πQ_desc hι hT hT' x₂ hx₂).choose_spec, hm])

-- BBD 1.2.1, p. 27
lemma hasKernel : HasKernel f₁ := ⟨_, isLimitKernelFork hι hT hT'⟩
lemma hasCokernel : HasCokernel f₁ := ⟨_, isColimitCokernelCofork hι hT hT'⟩

end

variable (ι)

def admissibleMorphism : MorphismProperty A := fun X₁ X₂ f₁ =>
  ∀ ⦃X₃ : C⦄ (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
    (_ : Triangle.mk (ι.map f₁) f₂ f₃ ∈ distTriang C),
  ∃ (K Q : A) (α : (ι.obj K)⟦(1 : ℤ)⟧ ⟶ X₃) (β : X₃ ⟶ (ι.obj Q))
    (γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧), Triangle.mk α β γ ∈ distTriang C

variable {ι}

lemma hasKernel_of_admissibleMorphism {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
    (hf₁ : admissibleMorphism ι f₁) :
    HasKernel f₁ := by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasKernel hι hT hT'

lemma hasCokernel_of_admissibleMorphism {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
    (hf₁ : admissibleMorphism ι f₁) :
    HasCokernel f₁ := by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasCokernel hι hT hT'

section

-- should be moved somewhere
instance hasZeroObject [HasTerminal A] : HasZeroObject A :=
  ⟨⊤_ A, by
    rw [IsZero.iff_id_eq_zero]
    apply Subsingleton.elim⟩

variable [HasFiniteProducts A]

noncomputable def isLimitKernelForkOfDistTriang {X₁ X₂ X₃ : A}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : ι.obj X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ι.map f₁) (ι.map f₂) f₃ ∈ distTriang C) :
    IsLimit (KernelFork.ofι f₁ (show f₁ ≫ f₂ = 0 from ι.map_injective (by
        erw [Functor.map_comp, comp_dist_triangle_mor_zero₁₂ _ hT, ι.map_zero]))) := by
  have hT' : Triangle.mk (𝟙 ((ι.obj X₁)⟦(1 : ℤ)⟧)) (0 : _ ⟶ ι.obj 0) 0 ∈ distTriang C := by
    refine' isomorphic_distinguished _ (contractible_distinguished
      (((ι ⋙ shiftFunctor C (1 : ℤ)).obj X₁))) _ _
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (IsZero.iso (by
      dsimp
      rw [IsZero.iff_id_eq_zero, ← ι.map_id, id_zero, ι.map_zero]) (isZero_zero C))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  refine' IsLimit.ofIsoLimit (AbelianSubcategory.isLimitKernelFork hι
    (rot_of_dist_triangle _ hT) hT') _
  exact Fork.ext (mulIso (-1) (Iso.refl _)) ((ι ⋙ shiftFunctor C (1 : ℤ)).map_injective
    (by simp))

variable (H : ∀ ⦃X₁ X₂ : A⦄ (f₁ : X₁ ⟶ X₂), admissibleMorphism ι f₁)

--lemma abelian : Abelian A := by
--  apply Abelian.mk'
--  sorry


end

end AbelianSubcategory

/-variable (t : TStructure C) [IsTriangulated C]

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

-/


end Triangulated

end CategoryTheory
