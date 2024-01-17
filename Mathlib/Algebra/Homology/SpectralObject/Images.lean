import Mathlib.Algebra.Homology.SpectralObject.Differentials
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

namespace CategoryTheory

open Category Limits ComposableArrows Preadditive

namespace Abelian

namespace SpectralObject

variable {C ι : Type*} [Category C] [Abelian C] [Category ι]
  (X : SpectralObject C ι)

section

variable (n : ℤ) {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)

-- this identifies to the image of `(X.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)` because
-- of the epi mono factorization that is obtained below
noncomputable def image : C := kernel ((X.H n).map (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂))

noncomputable def imageι : X.image n f₁ f₂ f₁₂ h₁₂ ⟶ (X.H n).obj (mk₁ f₁₂) :=
  kernel.ι _

instance : Mono (X.imageι n f₁ f₂ f₁₂ h₁₂) := by
  dsimp [imageι]
  infer_instance

noncomputable def imageπ : (X.H n).obj (mk₁ f₁) ⟶ X.image n f₁ f₂ f₁₂ h₁₂ :=
  kernel.lift _ ((X.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (by simp)

@[reassoc (attr := simp)]
lemma imageπ_ι :
    X.imageπ n f₁ f₂ f₁₂ h₁₂ ≫ X.imageι n f₁ f₂ f₁₂ h₁₂ =
      (X.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) := by
  simp [imageι, imageπ]

instance :
    Epi (X.imageπ n f₁ f₂ f₁₂ h₁₂) :=
  (ShortComplex.exact_iff_epi_kernel_lift _).1 (X.exact₂ n f₁ f₂ f₁₂ h₁₂)

lemma isZero_image (h : IsZero ((X.H n).obj (mk₁ f₁))) :
    IsZero (X.image n f₁ f₂ f₁₂ h₁₂) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (X.imageπ n f₁ f₂ f₁₂ h₁₂)]
  apply h.eq_of_src

lemma isIso_imageι (h : IsZero ((X.H n).obj (mk₁ f₂))) :
    IsIso (X.imageι n f₁ f₂ f₁₂ h₁₂) := by
  apply KernelFork.IsLimit.isIso_ι _ (kernelIsKernel ((X.H n).map (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂)))
  apply h.eq_of_tgt

section

variable {A : C} (x : A ⟶ (X.H n).obj (mk₁ f₁₂))
  (hx : x ≫ ((X.H n).map (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂)) = 0)

noncomputable def liftImage :
    A ⟶ X.image n f₁ f₂ f₁₂ h₁₂ :=
  kernel.lift _ x hx

@[reassoc (attr := simp)]
lemma liftImage_ι :
    X.liftImage n f₁ f₂ f₁₂ h₁₂ x hx ≫ X.imageι n f₁ f₂ f₁₂ h₁₂ = x := by
  apply kernel.lift_ι

end

section

variable {i₀' i₁' i₂' : ι} (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂')
  (f₁₂' : i₀' ⟶ i₂') (h₁₂' : f₁' ≫ f₂' = f₁₂')
  (α : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')

noncomputable def imageMap :
    X.image n f₁ f₂ f₁₂ h₁₂ ⟶ X.image n f₁' f₂' f₁₂' h₁₂' :=
  X.liftImage _ _ _ _ _ (X.imageι n f₁ f₂ f₁₂ h₁₂ ≫ (X.H n).map (homMk₁ (α.app 0) (α.app 2)
    (by dsimp; simpa only [← h₁₂, ← h₁₂'] using naturality' α 0 2))) (by
      have : twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂ ≫ homMk₁ (by exact α.app 0) (by exact α.app 2)
        (by dsimp; simpa only [← h₁₂, ← h₁₂'] using naturality' α 0 2) ≫ twoδ₁Toδ₀ f₁' f₂' f₁₂' h₁₂' =
        twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂ ≫ twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂ ≫
          homMk₁ (by exact α.app 1) (by exact α.app 2) (by exact naturality' α 1 2) := by
        ext
        · dsimp
          erw [id_comp, id_comp]
          exact (naturality' α 0 1).symm
        · dsimp
          erw [id_comp, comp_id]
      rw [← cancel_epi (X.imageπ n f₁ f₂ f₁₂ h₁₂), assoc, imageπ_ι_assoc, comp_zero,
        ← Functor.map_comp, ← Functor.map_comp, this, Functor.map_comp,
        Functor.map_comp, zero₂_assoc, zero_comp])

@[reassoc]
lemma imageMap_ι (β : mk₁ f₁₂ ⟶ mk₁ f₁₂') (hβ : β = (homMk₁ (α.app 0) (α.app 2)
    (by dsimp; simpa only [← h₁₂, ← h₁₂'] using naturality' α 0 2))) :
    X.imageMap n f₁ f₂ f₁₂ h₁₂ f₁' f₂' f₁₂' h₁₂' α ≫ X.imageι n f₁' f₂' f₁₂' h₁₂' =
      X.imageι n f₁ f₂ f₁₂ h₁₂ ≫ (X.H n).map β := by
  subst hβ
  simp [imageMap]

@[reassoc]
lemma π_imageMap (β : mk₁ f₁ ⟶ mk₁ f₁') (hβ : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)) :
    X.imageπ n f₁ f₂ f₁₂ h₁₂ ≫ X.imageMap n f₁ f₂ f₁₂ h₁₂ f₁' f₂' f₁₂' h₁₂' α =
      (X.H n).map β ≫ X.imageπ n f₁' f₂' f₁₂' h₁₂' := by
  rw [← cancel_mono (X.imageι n f₁' f₂' f₁₂' h₁₂')]
  simp only [assoc, imageπ_ι, X.imageMap_ι n f₁ f₂ f₁₂ h₁₂ f₁' f₂' f₁₂' h₁₂' α _ rfl,
    imageπ_ι_assoc, ← Functor.map_comp]
  subst hβ
  congr 1
  ext
  · dsimp
    erw [id_comp, comp_id]
  · exact naturality' α 1 2

end

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)

noncomputable def opcyclesIsoImage : X.opcycles n₀ n₁ hn₁ f₁ f₂ ≅ X.image n₁ f₁ f₂ f₁₂ h₁₂ := by
  let h := IsLimit.conePointUniqueUpToIso
    ((X.kernelSequenceOpcycles_exact n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).fIsKernel)
    (kernelIsKernel ((X.H n₁).map (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂)))
  exact h

@[reassoc (attr := simp)]
lemma opcyclesIsoImage_hom_ι :
    (X.opcyclesIsoImage n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).hom ≫ X.imageι n₁ f₁ f₂ f₁₂ h₁₂ =
      X.fromOpcycles n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (WalkingParallelPair.zero)

@[reassoc (attr := simp)]
lemma opcyclesIsoImage_inv_ι :
    (X.opcyclesIsoImage n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).inv ≫ X.fromOpcycles n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂ =
      X.imageι n₁ f₁ f₂ f₁₂ h₁₂ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (WalkingParallelPair.zero)

@[reassoc (attr := simp)]
lemma imageπ_opcyclesIsoImage_inv :
    X.imageπ n₁ f₁ f₂ f₁₂ h₁₂ ≫ (X.opcyclesIsoImage n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).inv =
      X.pOpcycles n₀ n₁ hn₁ f₁ f₂ := by
  simp only [← cancel_mono (X.fromOpcycles n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂),
    assoc, opcyclesIsoImage_inv_ι, imageπ_ι, p_fromOpcycles]

@[reassoc (attr := simp)]
lemma pOpcycles_opcyclesIsoImage_hom :
    X.pOpcycles n₀ n₁ hn₁ f₁ f₂ ≫ (X.opcyclesIsoImage n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).hom =
      X.imageπ n₁ f₁ f₂ f₁₂ h₁₂ := by
  simp only [← cancel_mono (X.imageι n₁ f₁ f₂ f₁₂ h₁₂),
    assoc, opcyclesIsoImage_hom_ι, p_fromOpcycles, imageπ_ι]

@[reassoc (attr := simp)]
lemma δ_imageπ :
    X.δ n₀ n₁ hn₁ f₁ f₂ ≫ X.imageπ n₁ f₁ f₂ f₁₂ h₁₂ = 0 := by
  simp only [← cancel_mono (X.imageι n₁ f₁ f₂ f₁₂ h₁₂), assoc, imageπ_ι, zero₁, zero_comp]

@[simps]
noncomputable def cokernelSequenceImage : ShortComplex C :=
    ShortComplex.mk _ _ (X.δ_imageπ n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂)

instance : Epi (X.cokernelSequenceImage n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).g := by
  dsimp
  infer_instance

lemma cokernelSequenceImage_exact :
    (X.cokernelSequenceImage n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (X.cokernelSequenceOpcycles_exact n₀ n₁ hn₁ f₁ f₂).gIsCokernel
    (Cofork.ext (X.opcyclesIsoImage n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂) (by simp))

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f₁) ⟶ A) (hx : X.δ n₀ n₁ hn₁ f₁ f₂ ≫ x = 0)
noncomputable def descImage :
    X.image n₁ f₁ f₂ f₁₂ h₁₂ ⟶ A :=
  (X.cokernelSequenceImage_exact n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).desc x hx

@[reassoc (attr := simp)]
lemma π_descImage :
    X.imageπ n₁ f₁ f₂ f₁₂ h₁₂ ≫ X.descImage n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂ x hx = x :=
  (X.cokernelSequenceImage_exact n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂).g_desc x hx

end

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₁₂₃ : i₀ ⟶ i₃) (h₁₂₃ : f₁ ≫ f₂ ≫ f₃ = f₁₂₃)

noncomputable def imageToE :
    X.image n₁ f₁₂ f₃ f₁₂₃ (by rw [← h₁₂₃, ← assoc, h₁₂]) ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
  X.descImage n₀ n₁ hn₁ f₁₂ f₃ f₁₂₃ _
    (X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) (by simp)

@[reassoc (attr := simp)]
lemma π_imageToE :
    X.imageπ n₁ f₁₂ f₃ f₁₂₃ _ ≫
      X.imageToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₁₂₃ h₁₂₃ =
      X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := by
  simp [imageToE]

@[reassoc (attr := simp)]
lemma imageToE_ιE :
    (X.opcyclesIsoImage n₀ n₁ hn₁ f₁₂ f₃ f₁₂₃ (by rw [← h₁₂₃, ← assoc, h₁₂])).hom ≫
      X.imageToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₁₂₃ h₁₂₃ ≫
      X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
        X.opcyclesMap n₀ n₁ hn₁ f₁₂ f₃ f₂ f₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) := by
  rw [← cancel_epi (X.opcyclesIsoImage n₀ n₁ hn₁ f₁₂ f₃ f₁₂₃ (by rw [← h₁₂₃, ← assoc, h₁₂])).inv,
    Iso.inv_hom_id_assoc, ← cancel_epi (X.imageπ n₁ f₁₂ f₃ f₁₂₃ _), π_imageToE_assoc,
    πE_ιE, toCycles_i_assoc, imageπ_opcyclesIsoImage_inv_assoc]
  symm
  apply X.p_opcyclesMap
  rfl

instance : Epi (X.imageToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₁₂₃ h₁₂₃) := by
  have : Epi (X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) :=
    epi_comp _ _
  exact epi_of_epi_fac (X.π_imageToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₁₂₃ h₁₂₃)

@[reassoc (attr := simp)]
lemma imageMap_threeδ₂Toδ₁_imageToE :
    X.imageMap n₁ f₁ f₂₃ f₁₂₃ (by rw [← h₁₂₃, h₂₃])
      f₁₂ f₃ f₁₂₃ (by rw [← h₁₂₃, ← assoc, h₁₂]) (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃) ≫
      X.imageToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₁₂₃ h₁₂₃ = 0 := by
  rw [← cancel_epi (X.imageπ n₁ f₁ f₂₃ f₁₂₃ _), comp_zero,
    X.π_imageMap_assoc n₁ f₁ f₂₃ f₁₂₃ _ f₁₂ f₃ f₁₂₃ _ (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃)
      (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) rfl, π_imageToE, H_map_twoδ₂Toδ₁_toCycles_assoc, zero_comp]

@[simps]
noncomputable def shortComplexImage : ShortComplex C :=
  ShortComplex.mk _ _
    (X.imageMap_threeδ₂Toδ₁_imageToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃)

instance : Mono (X.shortComplexImage n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃).f := by
  dsimp
  rw [mono_iff_cancel_zero]
  intro A x hx
  replace hx := hx =≫ X.imageι _ _ _ _ _
  rw [zero_comp, assoc] at hx
  rw [X.imageMap_ι n₁ f₁ f₂₃ f₁₂₃ _ f₁₂ f₃ f₁₂₃ _
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃) (𝟙 _) (by aesop_cat), Functor.map_id, comp_id] at hx
  rw [← cancel_mono (X.imageι _ _ _ _ _), zero_comp, hx]

instance : Epi (X.shortComplexImage n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃).g := by
  dsimp
  infer_instance

@[simps]
noncomputable def shortComplexImageHom :
    X.cokernelSequenceE'' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ ⟶
      X.shortComplexImage n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃ where
  τ₁ := X.imageπ n₁ f₁ f₂₃ f₁₂₃ _
  τ₂ := (X.opcyclesIsoImage n₀ n₁ hn₁ f₁₂ f₃ f₁₂₃ _).hom
  τ₃ := 𝟙 _
  comm₁₂ := by
    dsimp
    simp only [assoc, pOpcycles_opcyclesIsoImage_hom]
    apply X.π_imageMap
    rfl
  comm₂₃ := by
    dsimp
    rw [← cancel_mono (X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃), assoc,
      ← cancel_epi (X.opcyclesIsoImage n₀ n₁ hn₁ f₁₂ f₃ f₁₂₃ (by rw [← h₁₂, assoc, h₁₂₃])).inv,
      imageToE_ιE, comp_id, opcyclesToE_ιE]

instance :
    Epi (X.shortComplexImageHom n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃).τ₁ := by
  dsimp
  infer_instance

instance :
    IsIso (X.shortComplexImageHom n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃).τ₂ := by
  dsimp
  infer_instance

instance :
    IsIso (X.shortComplexImageHom n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃).τ₃ := by
  dsimp
  infer_instance

lemma shortComplexImage_exact :
    (X.shortComplexImage n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃).Exact := by
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (X.shortComplexImageHom n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃)]
  apply X.cokernelSequenceE''_exact

lemma shortComplexImage_shortExact :
    (X.shortComplexImage n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃ f₁₂₃ h₁₂₃).ShortExact where
  exact := by apply shortComplexImage_exact

end

end SpectralObject

end Abelian

end CategoryTheory
