import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianCategoryLemmas
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

namespace CategoryTheory

open Category Limits Triangulated Pretriangulated TStructure ObjectProperty

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [CategoryTheory.IsTriangulated C]
  [CategoryTheory.IsTriangulated D]


scoped [ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.zero'

open ZeroObject Limits Preadditive Pretriangulated CategoryTheory.Functor

variable (F : C ⥤ D) [F.CommShift ℤ] (t₁ : TStructure C) (t₂ : TStructure D)
variable [F.IsTriangulated]

local instance : t₁.HasHeart := hasHeartFullSubcategory t₁
local instance : t₂.HasHeart := hasHeartFullSubcategory t₂
noncomputable local instance : t₁.HasHomology₀ := t₁.hasHomology₀
noncomputable local instance : t₂.HasHomology₀ := t₂.hasHomology₀

noncomputable local instance : t₂.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

abbrev AcyclicObject (X : t₁.Heart) := t₂.heart (F.obj X.1)

omit [IsTriangulated C] [F.CommShift ℤ] [F.IsTriangulated] in
lemma AcyclicImageHasZeroHomology {X : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X) (n : ℤ)
    (hn : n ≠ 0) : IsZero ((t₂.homology n).obj (F.obj X.1)) := by
  simp only [AcyclicObject, mem_heart_iff] at hX
  by_cases h : n ≥ 0
  · have := hX.1
    exact t₂.isZero_homology_of_isLE (F.obj X.1) n 0 (lt_iff_le_and_ne.mpr ⟨h, Ne.symm hn⟩)
  · have := hX.2
    exact t₂.isZero_homology_of_isGE (F.obj X.1) n 0 (lt_iff_not_le.mpr h)

abbrev AcyclicCategory := FullSubcategory (AcyclicObject F t₁ t₂)

namespace Functor

abbrev FromAcyclic : (AcyclicCategory F t₁ t₂) ⥤ t₂.Heart := by
  refine FullSubcategory.lift t₂.heart
    (fullSubcategoryInclusion (AcyclicObject F t₁ t₂) ⋙ t₁.ιHeart ⋙ F) ?_
  intro ⟨_, h⟩
  simp only [comp_obj, fullSubcategoryInclusion.obj]
  exact h

abbrev FromHeart : t₁.Heart ⥤ D := t₁.ιHeart ⋙ F

instance : Functor.Additive (F.FromHeart t₁) where
  map_add := by
    intro X Y f g
    simp only [comp_obj, comp_map, map_add]

noncomputable abbrev FromHeartToHeart : t₁.Heart ⥤ t₂.Heart :=
  t₁.ιHeart ⋙ F ⋙ t₂.homology 0

def AcyclicToHeart : (AcyclicCategory F t₁ t₂) ⥤ t₁.Heart := fullSubcategoryInclusion _

end Functor

namespace AcyclicCategory

instance closedUnderIsomorphisms : IsClosedUnderIsomorphisms (AcyclicObject F t₁ t₂) := by
  refine IsClosedUnderIsomorphisms.mk ?_
  intro _ _ e hX
  change t₂.heart _
  exact IsClosedUnderIsomorphisms.of_iso ((F.FromHeart t₁).mapIso e) hX

variable (X Y : t₁.Heart)

omit [IsTriangulated C] [IsTriangulated D] in
lemma zero {X : t₁.Heart} (hX : IsZero X) : AcyclicObject F t₁ t₂ X := by
  simp only [AcyclicObject]
  exact IsClosedUnderIsomorphisms.of_iso (((F.FromHeart t₁).mapIso hX.isoZero).trans
    (F.FromHeart t₁).mapZeroObject).symm t₂.zero_mem_heart

lemma prod {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X) (hY : AcyclicObject F t₁ t₂ Y) :
    AcyclicObject F t₁ t₂ (X ⨯ Y) := by
  simp only [AcyclicObject]
  have : PreservesLimit (pair X Y) t₁.ιHeart := sorry -- not synthesized anymore
  have := PreservesLimitPair.iso t₁.ιHeart X Y
  exact IsClosedUnderIsomorphisms.of_iso (PreservesLimitPair.iso (F.FromHeart t₁) X Y).symm
      (prod_mem_heart t₂ _ _ hX hY)

instance : HasTerminal (AcyclicCategory F t₁ t₂) := by
  let Z : AcyclicCategory F t₁ t₂ := ⟨0, zero F t₁ t₂ (isZero_zero t₁.Heart)⟩
  have : ∀ X, Inhabited (X ⟶ Z) := fun X => ⟨0⟩
  have : ∀ X, Unique (X ⟶ Z) := fun X =>
    { uniq := fun f => (fullSubcategoryInclusion (AcyclicObject F t₁ t₂)).map_injective
          ((isZero_zero t₁.Heart).eq_of_tgt _ _) }
  exact hasTerminal_of_unique Z

instance : HasBinaryProducts (AcyclicCategory F t₁ t₂) := by
  apply hasLimitsOfShape_of_closedUnderLimits
  intro P c hc H
  exact prop_of_iso (AcyclicObject F t₁ t₂)
    (limit.isoLimitCone ⟨_, (IsLimit.postcomposeHomEquiv (diagramIsoPair P) _).symm hc⟩)
    (prod F t₁ t₂ (H _) (H _))

instance : HasFiniteProducts (AcyclicCategory F t₁ t₂) :=
  hasFiniteProducts_of_has_binary_and_terminal

instance : HasZeroObject (AcyclicCategory F t₁ t₂) := sorry

instance : HasBinaryBiproducts (AcyclicCategory F t₁ t₂) := sorry

end AcyclicCategory

instance : Functor.Additive (F.FromAcyclic t₁ t₂) where
  map_add := by
    intro X Y f g
    simp only [FullSubcategory.lift_map, Functor.comp_map, fullSubcategoryInclusion.obj,
      fullSubcategoryInclusion.map, Functor.map_add]

instance : Functor.Additive (F.AcyclicToHeart t₁ t₂) where
  map_add := by
    intro X Y f g
    simp only [Functor.AcyclicToHeart, fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map]

omit [IsTriangulated D] in
lemma AcyclicExtension {S : ShortComplex t₁.Heart} (SE : S.ShortExact)
    (hS₁ : AcyclicObject F t₁ t₂ S.X₁) (hS₃ : AcyclicObject F t₁ t₂ S.X₃) :
    AcyclicObject F t₁ t₂ S.X₂ := by
  set DT' := F.map_distinguished _ (heartShortExactTriangle_distinguished t₁ S SE)
  simp only [AcyclicObject] at hS₁ hS₃ ⊢
  rw [t₂.mem_heart_iff] at hS₁ hS₃ ⊢
  constructor
  · exact t₂.isLE₂ _ DT' 0 hS₁.1 hS₃.1
  · exact t₂.isGE₂ _ DT' 0 hS₁.2 hS₃.2

noncomputable abbrev ShortExactComplexToImageDistTriangle {S : ShortComplex t₁.Heart}
    (he : S.ShortExact) : Pretriangulated.Triangle D :=
  F.mapTriangle.obj (heartShortExactTriangle t₁ _ he)

omit [IsTriangulated D] in
lemma ShortExactComplexToImageDistTriangle_distinguished {S : ShortComplex t₁.Heart}
    (he : S.ShortExact) : ShortExactComplexToImageDistTriangle F t₁ he ∈ distinguishedTriangles :=
  F.map_distinguished _ (heartShortExactTriangle_distinguished t₁ _ he)

noncomputable abbrev ShortExactComplexImageIsoHomology
    {S : ShortComplex t₁.Heart} (he : S.ShortExact) :
    ShortComplex.mk ((t₂.homology 0).map (ShortExactComplexToImageDistTriangle F t₁ he).mor₁)
    ((t₂.homology 0).map (ShortExactComplexToImageDistTriangle F t₁ he).mor₂)
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
      (ShortExactComplexToImageDistTriangle_distinguished F t₁ he), Functor.map_zero])
    ≅ (F.FromHeartToHeart t₁ t₂).mapShortComplex.obj S := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)

lemma ShortExactComplexImageExact {S : ShortComplex t₁.Heart} (he : S.ShortExact) :
    ((F.FromHeartToHeart t₁ t₂).mapShortComplex.obj S).Exact :=
  ShortComplex.exact_of_iso (ShortExactComplexImageIsoHomology F t₁ t₂ he)
  (t₂.homology_exact₂ _ (ShortExactComplexToImageDistTriangle_distinguished F t₁ he) 0)

lemma MonoOfMonoAcyclicCokernel {X Y : t₁.Heart} (f : X ⟶ Y) (hm : Mono f)
    (hv : IsZero ((t₂.homology (-1 : ℤ)).obj (F.obj (cokernel f).1))) :
    Mono ((F.FromHeartToHeart t₁ t₂).map f) :=
  (ShortComplex.exact_iff_mono _ (IsZero.eq_zero_of_src hv _)).mp (t₂.homology_exact₁ _
  (ShortExactComplexToImageDistTriangle_distinguished F t₁ (monoCokernelComplexShortExact f hm))
  (-1 : ℤ) 0 (by simp))

lemma EpiOfEpiAcyclicKernel {X Y : t₁.Heart} (f : X ⟶ Y) (he : Epi f)
    (hv : IsZero ((t₂.homology (1 : ℤ)).obj (F.obj (kernel f).1))) :
    Epi ((F.FromHeartToHeart t₁ t₂).map f) :=
  (ShortComplex.exact_iff_epi _ (IsZero.eq_zero_of_tgt hv _)).mp (t₂.homology_exact₃ _
  (ShortExactComplexToImageDistTriangle_distinguished F t₁ (epiKernelComplexShortExact f he))
  (0 : ℤ) 1 (by simp))

lemma ShortExactComplexImageShortExact {S : ShortComplex t₁.Heart} (he : S.ShortExact)
    (hv₁ : IsZero ((t₂.homology (1 : ℤ)).obj (F.obj S.X₁.1)))
    (hv₂ : IsZero ((t₂.homology (-1 : ℤ)).obj (F.obj S.X₃.1))) :
    ((F.FromHeartToHeart t₁ t₂).mapShortComplex.obj S).ShortExact where
  exact := ShortExactComplexImageExact F t₁ t₂ he
  mono_f := MonoOfMonoAcyclicCokernel F t₁ t₂ S.f he.mono_f
    (IsZero.of_iso hv₂ ((t₂.homology (-1 : ℤ)).mapIso (F.mapIso
    ((fullSubcategoryInclusion _).mapIso (IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel S.f) he.gIsCokernel)))))
  epi_g := EpiOfEpiAcyclicKernel F t₁ t₂ S.g he.epi_g
    (IsZero.of_iso hv₁ ((t₂.homology (1 : ℤ)).mapIso (F.mapIso
    ((fullSubcategoryInclusion _).mapIso (IsLimit.conePointUniqueUpToIso
    (kernelIsKernel S.g) he.fIsKernel)))))

lemma ShortExactComplexImageShortExact' {S : ShortComplex t₁.Heart} (he : S.ShortExact)
    (hv₁ : AcyclicObject F t₁ t₂ S.X₁) (hv₂ : AcyclicObject F t₁ t₂ S.X₃) :
    ((F.FromHeartToHeart t₁ t₂).mapShortComplex.obj S).ShortExact :=
  ShortExactComplexImageShortExact F t₁ t₂ he
  (AcyclicImageHasZeroHomology F t₁ t₂ hv₁ (1 : ℤ) (by simp))
  (AcyclicImageHasZeroHomology F t₁ t₂ hv₂ (-1 : ℤ) (by simp))

@[simps!]
noncomputable def imageFactorisationOfAcyclic {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : AcyclicObject F t₁ t₂ (cokernel f)) (h₂ : AcyclicObject F t₁ t₂ (kernel f)) :
    ImageFactorisation ((F.FromHeartToHeart t₁ t₂).map f) := by
  refine imageFactorisationOfNormalEpi (C := t₂.Heart) _ ?_ ?_
  · refine {I := (F.FromHeartToHeart t₁ t₂).obj (Abelian.image f),
            e := (F.FromHeartToHeart t₁ t₂).map (Abelian.factorThruImage _),
            m := (F.FromHeartToHeart t₁ t₂).map (Abelian.image.ι _),
            m_mono := ?_, fac := ?_}
    · refine MonoOfMonoAcyclicCokernel F t₁ t₂ (Abelian.image.ι f) inferInstance
        (@isZero_homology_of_isGE _ _ _ _ _ _ _ t₂ _ _ _ _ (-1 : ℤ) 0 (by simp only [Int.reduceNeg,
          Left.neg_neg_iff, zero_lt_one]) ?_)
      have := Limits.IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f)
       (Limits.isCokernelEpiComp (cokernelIsCokernel (Abelian.image.ι f))
        (Abelian.factorThruImage f) (Abelian.image.fac f).symm)
      have := IsClosedUnderIsomorphisms.of_iso this h₁
      simp only [AcyclicObject, mem_heart_iff] at this
      exact this.2
    · rw [← map_comp, Abelian.image.fac]
  · refine @normalEpiOfEpi (C := t₂.Heart) _ _ _ _ _ _  ?_
    refine EpiOfEpiAcyclicKernel F t₁ t₂ (Abelian.factorThruImage f) inferInstance
      (@isZero_homology_of_isLE _ _ _ _ _ _ _ t₂ _ _ _ _ _ (1 : ℤ) 0 zero_lt_one ?_)
    have := Limits.IsLimit.conePointUniqueUpToIso (kernelIsKernel f) (Limits.isKernelCompMono
      (kernelIsKernel (Abelian.factorThruImage f)) (Abelian.image.ι f) (Abelian.image.fac f).symm)
    have := IsClosedUnderIsomorphisms.of_iso this h₂
    simp only [AcyclicObject, mem_heart_iff] at this
    exact this.1

noncomputable def isoImageOfAcyclic {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : AcyclicObject F t₁ t₂ (cokernel f)) (h₂ : AcyclicObject F t₁ t₂ (kernel f)) :
    (F.FromHeartToHeart t₁ t₂).obj (Abelian.image f) ≅
    Abelian.image ((F.FromHeartToHeart t₁ t₂).map f) :=
  (IsImage.isoExt (imageFactorisationOfAcyclic F t₁ t₂ f h₁ h₂).isImage (Limits.Image.isImage
  ((F.FromHeartToHeart t₁ t₂).map f))).trans (Abelian.imageIsoImage _).symm

lemma isoImageOfAcyclic_comp_ι {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : AcyclicObject F t₁ t₂ (cokernel f)) (h₂ : AcyclicObject F t₁ t₂ (kernel f)) :
    (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom ≫ Abelian.image.ι ((F.FromHeartToHeart t₁ t₂).map f) =
    (F.FromHeartToHeart t₁ t₂).map (Abelian.image.ι f) := by
  simp only [isoImageOfAcyclic]
  rw [Iso.trans_hom, Iso.symm_hom, assoc, image_compat]
  erw [IsImage.isoExt_hom_m]
  rfl

lemma factorThruImage_comp_IsoImageOfAcyclic {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : AcyclicObject F t₁ t₂ (cokernel f)) (h₂ : AcyclicObject F t₁ t₂ (kernel f)) :
    (F.FromHeartToHeart t₁ t₂).map (Abelian.factorThruImage f) ≫
    (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom
    = Abelian.factorThruImage ((F.FromHeartToHeart t₁ t₂).map f) := by
  rw [← cancel_mono (Abelian.image.ι ((F.FromHeartToHeart t₁ t₂).map f)), assoc,
  isoImageOfAcyclic_comp_ι, ← map_comp, Abelian.image.fac, Abelian.image.fac]

lemma IsIsoKernelComparisonOfAcyclic_mono {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image f)) :
    Mono (kernelComparison f (F.FromHeartToHeart t₁ t₂)) := by
  refine @mono_of_mono_fac _ _ _ _ _ _ (kernel.ι _) ((F.FromHeartToHeart t₁ t₂).map (kernel.ι f))
    ?_ (by rw [kernelComparison_comp_ι])
  refine MonoOfMonoAcyclicCokernel F t₁ t₂ (kernel.ι f) inferInstance (@isZero_homology_of_isGE
    _ _ _ _ _ _ _ t₂ _ _ _ _ (-1 : ℤ) 0 (by simp only [Int.reduceNeg, Left.neg_neg_iff,
    zero_lt_one]) ?_)
  have := IsClosedUnderIsomorphisms.of_iso (Abelian.coimageIsoImage _).symm h₃
  simp only [AcyclicObject, mem_heart_iff] at this
  exact this.2

lemma IsIsoKernelComparisonOfAcyclic_epi {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : AcyclicObject F t₁ t₂ (cokernel f)) (h₂ : AcyclicObject F t₁ t₂ (kernel f))
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image f)) :
    Epi (kernelComparison f (F.FromHeartToHeart t₁ t₂)) := by
  set R₁ := ((F.FromHeartToHeart t₁ t₂).mapShortComplex.obj (ShortComplex.mk (kernel.ι f)
    (Abelian.factorThruImage f)
    (by rw [← cancel_mono (Abelian.image.ι f), assoc, Abelian.image.fac, zero_comp,
      kernel.condition f]))).toComposableArrows
  set R₂ := (ShortComplex.mk (kernel.ι ((F.FromHeartToHeart t₁ t₂).map f))
    (Abelian.factorThruImage ((F.FromHeartToHeart t₁ t₂).map f))
    (by rw [← cancel_mono (Abelian.image.ι _), zero_comp, assoc, Abelian.image.fac,
    kernel.condition])).toComposableArrows
  have hR₁ : R₁.Exact := (ShortExactComplexImageShortExact' F t₁ t₂
    (kernelImageComplexShortExact f) h₂ h₃).exact.exact_toComposableArrows
  have hR₂ : R₂.Exact := (kernelImageComplexShortExact _).exact.exact_toComposableArrows
  set φ : R₁ ⟶ R₂ := by
    refine ComposableArrows.homMk ?_ ?_
    · intro i
      match i with
      | 0 => exact kernelComparison f (F.FromHeartToHeart t₁ t₂)
      | 1 => exact 𝟙 _
      | 2 => exact (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom
    · intro i _
      match i with
      | 0 => erw [kernelComparison_comp_ι, comp_id]; rfl
      | 1 => erw [factorThruImage_comp_IsoImageOfAcyclic, id_comp]; rfl
  refine Abelian.epi_of_mono_of_epi_of_mono φ hR₁ hR₂ ?_ ?_ ?_
  · change Mono (kernel.ι _); exact inferInstance
  · change Epi (𝟙 _); exact inferInstance
  · change Mono (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom; exact inferInstance

noncomputable def IsIsoKernelComparisonOfAcyclic {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : AcyclicObject F t₁ t₂ (cokernel f)) (h₂ : AcyclicObject F t₁ t₂ (kernel f))
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image f)) :
    IsIso (kernelComparison f (F.FromHeartToHeart t₁ t₂)) :=
  @isIso_of_mono_of_epi _ _ _ _ _ _ (IsIsoKernelComparisonOfAcyclic_mono F t₁ t₂ f h₃)
  (IsIsoKernelComparisonOfAcyclic_epi F t₁ t₂ f h₁ h₂ h₃)

lemma IsIsoCokernelComparisonOfAcyclic_epi {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image f)) :
    Epi (cokernelComparison f (F.FromHeartToHeart t₁ t₂)) := by
  simp only [AcyclicObject, mem_heart_iff] at h₃
  exact @epi_of_epi_fac _ _ _ _ _ (cokernel.π _) _ ((F.FromHeartToHeart t₁ t₂).map (cokernel.π f))
    (EpiOfEpiAcyclicKernel F t₁ t₂ (cokernel.π f) inferInstance (@isZero_homology_of_isLE
    _ _ _ _ _ _ _ t₂ _ _ _ _ _ (1 : ℤ) 0 zero_lt_one h₃.1)) (by rw [π_comp_cokernelComparison])


lemma IsIsoCokernelComparisonOfAcyclic_mono {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : AcyclicObject F t₁ t₂ (cokernel f)) (h₂ : AcyclicObject F t₁ t₂ (kernel f))
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image f)) :
    Mono (cokernelComparison f (F.FromHeartToHeart t₁ t₂)) := by
  set R₂ := ((F.FromHeartToHeart t₁ t₂).mapShortComplex.obj (ShortComplex.mk (Abelian.image.ι f)
    (Limits.cokernel.π f)
    (by simp only [equalizer_as_kernel, kernel.condition]))).toComposableArrows
  set R₁ := (ShortComplex.mk (Abelian.image.ι ((F.FromHeartToHeart t₁ t₂).map f))
    (cokernel.π ((F.FromHeartToHeart t₁ t₂).map f))
    (by simp only [comp_obj, Functor.comp_map, equalizer_as_kernel,
    kernel.condition])).toComposableArrows
  have hR₂ : R₂.Exact := (ShortExactComplexImageShortExact' F t₁ t₂ (epiKernelComplexShortExact
    (cokernel.π f) inferInstance) h₃ h₁).exact.exact_toComposableArrows
  have hR₁ : R₁.Exact := (kernelComplexExact _).exact_toComposableArrows
  set φ : R₁ ⟶ R₂ := by
    refine ComposableArrows.homMk ?_ ?_
    · intro i
      match i with
      | 0 => exact (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).inv
      | 1 => exact 𝟙 _
      | 2 => exact cokernelComparison _ _
    · intro i _
      match i with
      | 0 => rw [← cancel_epi (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom]; erw [comp_id]
             rw [← assoc, Iso.hom_inv_id, id_comp]
             erw [isoImageOfAcyclic_comp_ι]; rfl
      | 1 => erw [id_comp, π_comp_cokernelComparison]; rfl
  refine Abelian.mono_of_epi_of_epi_of_mono φ hR₁ hR₂ ?_ ?_ ?_
  · change Epi (cokernel.π _); exact inferInstance
  · change Epi (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).inv; exact inferInstance
  · change Mono (𝟙 _); exact inferInstance

noncomputable def IsIsoCokernelComparisonOfAcyclic {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : AcyclicObject F t₁ t₂ (cokernel f)) (h₂ : AcyclicObject F t₁ t₂ (kernel f))
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image f)) :
    IsIso (cokernelComparison f (F.FromHeartToHeart t₁ t₂)) :=
  @isIso_of_mono_of_epi _ _ _ _ _ _ (IsIsoCokernelComparisonOfAcyclic_mono F t₁ t₂ f h₁ h₂ h₃)
  (IsIsoCokernelComparisonOfAcyclic_epi F t₁ t₂ f h₃)

noncomputable def ShortExactComplexHomology {S : ShortComplex t₁.Heart} (hS : S.ShortExact)
    (hS₁ : AcyclicObject F t₁ t₂ S.X₂) {n : ℤ} (hn : n ≠ -1 ∧ n ≠ 0) :
    (t₂.homology n).obj (F.obj S.X₃.1) ≅ (t₂.homology (n + 1)).obj (F.obj S.X₁.1) := by
  set T := ShortExactComplexToImageDistTriangle F t₁ hS
  have hT : T ∈ distinguishedTriangles := ShortExactComplexToImageDistTriangle_distinguished F t₁ hS
  set f := t₂.homologyδ (ShortExactComplexToImageDistTriangle F t₁ hS) n (n + 1) rfl
  have h₁ : Mono f := by
    refine (ShortComplex.exact_iff_mono _ (Limits.zero_of_source_iso_zero _ ?_)).mp
      (t₂.homology_exact₃ _ hT n (n + 1) rfl)
    change (t₂.homology n).obj (F.obj S.X₂.1) ≅ 0
    refine Limits.IsZero.isoZero ?_
    by_cases hn' : 0 ≤ n
    · letI : t₂.IsLE (F.obj S.X₂.1) 0 := {le := hS₁.1}
      exact t₂.isZero_homology_of_isLE _ n 0 (lt_iff_le_and_ne.mpr ⟨hn', Ne.symm hn.2⟩)
    · letI : t₂.IsGE (F.obj S.X₂.1) 0 := {ge := hS₁.2}
      exact t₂.isZero_homology_of_isGE _ n 0 (lt_iff_not_le.mpr hn')
  have h₂ : Epi f := by
    refine (ShortComplex.exact_iff_epi _ (Limits.zero_of_target_iso_zero _ ?_)).mp
      (t₂.homology_exact₁ _ hT n (n + 1) rfl)
    change (t₂.homology (n + 1)).obj (F.obj S.X₂.1) ≅ 0
    refine Limits.IsZero.isoZero ?_
    by_cases hn' : 0 ≤ n
    · letI : t₂.IsLE (F.obj S.X₂.1) 0 := {le := hS₁.1}
      exact t₂.isZero_homology_of_isLE _ (n + 1) 0 (Int.lt_add_one_iff.mpr hn')
    · letI : t₂.IsGE (F.obj S.X₂.1) 0 := {ge := hS₁.2}
      refine t₂.isZero_homology_of_isGE _ (n + 1) 0 ?_
      rw [lt_iff_le_and_ne, Int.add_one_le_iff, and_iff_right (lt_iff_not_le.mpr hn'), ne_eq,
          ← eq_neg_iff_add_eq_zero]
      exact hn.1
  exact @asIso _ _ _ _ f ((isIso_iff_mono_and_epi f).mpr ⟨h₁, h₂⟩)

noncomputable def IsoCohomologyOfAcyclicAndExact (S : CochainComplex t₁.Heart ℤ) (r k l m : ℤ)
    (hrk : r + 1 = k) (hkl : k = l) (hlm : l + 1 = m) (h₁ : AcyclicObject F t₁ t₂ (S.X r))
    (h₂ : S.ExactAt l) {n : ℤ} (hn : n ≠ -1 ∧ n ≠ 0) :
    (t₂.homology n).obj (F.obj (Limits.kernel (S.d l m)).1) ≅ (t₂.homology (n + 1)).obj
    (F.obj (Limits.kernel (S.d r k)).1) :=
  (((t₂.homology n).mapIso (F.mapIso ((fullSubcategoryInclusion _).mapIso
  ((S.sc' r l m).isoAbelianImageToKernelOfExact ((S.exactAt_iff' r l m
  (by simp only [CochainComplex.prev]; linarith [hrk, hkl])
  (by simp only [CochainComplex.next, hlm])).mp h₂))))).symm.trans
  (ShortExactComplexHomology F t₁ t₂ (kernelImageComplexShortExact (S.d r l)) h₁ hn)).trans
  ((t₂.homology (n + 1)).mapIso (F.mapIso ((fullSubcategoryInclusion _).mapIso
  (kernel.mapIso (S.d r l) (S.d r k) (Iso.refl _) (S.XIsoOfEq hkl.symm)
  (by simp only [HomologicalComplex.d_comp_XIsoOfEq_hom, Iso.refl_hom, id_comp])))))

noncomputable def RightAcyclicKer_aux (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ} (hkl : k + 1 = l)
    (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), i ≤ k → AcyclicObject F t₁ t₂ (S.X i)) (n : ℕ) :
    (t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1) ≅ (t₂.homology (r + n)).obj
    (F.obj (Limits.kernel (S.d (k - n) (l - n))).1) := by
  induction' n with n hn
  · simp only [CharP.cast_eq_zero, add_zero, Int.Nat.cast_ofNat_Int]
    erw [sub_zero, sub_zero]
  · have : r + ↑(n + 1) = (r + n) + 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [this]
    have : k - ↑(n + 1) = (k - n) - 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [this]
    have : l - ↑(n + 1) = (l - n) - 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [this]
    refine hn.trans (IsoCohomologyOfAcyclicAndExact F t₁ t₂ S (k - n - 1) (l - n - 1) (k - n)
      (l - n) (by linarith) (by linarith [hkl]) (by linarith) (hk2 (k - n - 1) (by linarith))
      (hk1 (k - n) (by linarith)) (n := r + n) ⟨by linarith [hr], by linarith [hr]⟩)

lemma RightAcyclicKerOfBoundedComplex (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), i ≤ k → AcyclicObject F t₁ t₂ (S.X i)) {a : ℤ}
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j)) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1)) := by
  refine IsZero.of_iso ?_ (RightAcyclicKer_aux F t₁ t₂ S hkl hr hk1 hk2 (k - a).natAbs)
  suffices h : IsZero (kernel (S.d (k - ↑(k - a).natAbs) (l - ↑(k - a).natAbs))) by
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    change IsZero ((fullSubcategoryInclusion _).obj _)
    refine Functor.map_isZero _ h
  refine IsZero.of_mono (kernel.ι (S.d (k - (k - a).natAbs) (l - (k - a).natAbs))) (ha _ ?_)
  rw [tsub_le_iff_right, ← tsub_le_iff_left]; exact Int.le_natAbs

lemma RightAcyclicKerOfBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), i ≤ k → AcyclicObject F t₁ t₂ (S.X i)) {d : ℤ}
    (hd : ∀ (X : t₁.Heart) (j : ℤ), d ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1)) := by
  refine IsZero.of_iso (hd _ _ ?_) (RightAcyclicKer_aux F t₁ t₂ S hkl hr hk1 hk2 (d - r).natAbs)
  rw [← tsub_le_iff_left]; exact Int.le_natAbs

noncomputable def LeftAcyclicKer_aux (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), k ≤ i → AcyclicObject F t₁ t₂ (S.X i)) (n : ℕ) :
    (t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1) ≅ (t₂.homology (r - n)).obj
    (F.obj (Limits.kernel (S.d (k + n) (l + n))).1) := by
  induction' n with n hn
  · simp only [CharP.cast_eq_zero, sub_zero, Int.Nat.cast_ofNat_Int]
    erw [add_zero, add_zero]
  · refine hn.trans ?_
    have : r - n = r - (n + 1) + 1 := by ring
    erw [this]
    exact (IsoCohomologyOfAcyclicAndExact F t₁ t₂ S (k + n) (l + n) (k + (n + 1))
      (l + (n + 1)) (by linarith) (by linarith) (by linarith)
      (hk2 (k + n) (by linarith)) (hk1 (k + (n + 1)) (by linarith)) (n := r - (n + 1))
      ⟨by linarith [hr], by linarith [hr]⟩).symm

lemma LeftAcyclicKerOfBoundedComplex (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), k ≤ i → AcyclicObject F t₁ t₂ (S.X i)) {b : ℤ}
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1)) := by
  refine IsZero.of_iso ?_ (LeftAcyclicKer_aux F t₁ t₂ S hkl hr hk1 hk2 (b - k).natAbs)
  suffices h : IsZero (kernel (S.d (k + ↑(b - k).natAbs) (l + ↑(b - k).natAbs))) by
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    change IsZero ((fullSubcategoryInclusion _).obj _)
    refine Functor.map_isZero _ h
  refine IsZero.of_mono (kernel.ι (S.d (k + (b - k).natAbs) (l + (b - k).natAbs))) (hb _ ?_)
  rw [← tsub_le_iff_left]; exact Int.le_natAbs

lemma LeftAcyclicKerOfBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), k ≤ i → AcyclicObject F t₁ t₂ (S.X i)) {c : ℤ}
    (hc : ∀ (X : t₁.Heart) (j : ℤ), j ≤ c → IsZero ((t₂.homology j).obj (F.obj X.1))) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1)) := by
  refine IsZero.of_iso (hc _ _ ?_) (LeftAcyclicKer_aux F t₁ t₂ S hkl hr hk1 hk2 (r - c).natAbs)
  rw [tsub_le_iff_left, ← tsub_le_iff_right]; exact Int.le_natAbs

variable [NonDegenerate t₂]

lemma AcyclicKerOfBoundedExactComplex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k l : ℤ) (hkl : k + 1 = l) :
    AcyclicObject F t₁ t₂ (Limits.kernel (S.d k l)) := by
  simp only [AcyclicObject]
  refine isHeart_of_isZero_homology t₂ _ ?_
  intro j hj
  rw [ne_iff_lt_or_gt] at hj
  cases hj with
  | inl h => exact LeftAcyclicKerOfBoundedComplex F t₁ t₂ S hkl h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) hb
  | inr h => exact RightAcyclicKerOfBoundedComplex F t₁ t₂ S hkl h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) ha

lemma AcyclicKerOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b: ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (k l : ℤ) (hkl : k + 1 = l) :
    AcyclicObject F t₁ t₂ (Limits.kernel (S.d k l)) := by
  simp only [AcyclicObject]
  refine isHeart_of_isZero_homology t₂ _ ?_
  intro j hj
  rw [ne_iff_lt_or_gt] at hj
  cases hj with
  | inl h => exact LeftAcyclicKerOfBoundedFunctor F t₁ t₂ S hkl h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) ha
  | inr h => exact RightAcyclicKerOfBoundedFunctor F t₁ t₂ S hkl h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) hb

lemma AcyclicImageOfBoundedExactComplex (S : CochainComplex t₁.Heart ℤ) {a b: ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k l : ℤ) (hkl : k + 1 = l) :
    AcyclicObject F t₁ t₂ (Abelian.image (S.d k l)) := by
  refine IsClosedUnderIsomorphisms.of_iso ?_ (AcyclicKerOfBoundedExactComplex F t₁ t₂ S hexact
    hacy ha hb (k + 1) (l + 1) (by linarith))
  set e : S.sc l ≅ S.sc' k l (l + 1) :=
    S.isoSc' k l (l + 1) (by simp only [hkl.symm, CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next])
  have := ShortComplex.imageToKernelIsIsoOfExact (IsZero.of_iso
    ((S.exactAt_iff_isZero_homology _).mp (hexact l)) (ShortComplex.homologyMapIso e).symm)
  exact ((asIso (S.sc' k l (l + 1)).abelianImageToKernel).trans (kernel.mapIso (S.d l (l + 1))
    (S.d (k + 1) (l + 1)) (S.XIsoOfEq hkl.symm) (Iso.refl _)
    (by simp only [Iso.refl_hom, comp_id, HomologicalComplex.XIsoOfEq_hom_comp_d]))).symm

lemma AcyclicImageOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k l : ℤ)
    (hkl : k + 1 = l) :
    AcyclicObject F t₁ t₂ (Abelian.image (S.d k l)) := by
  refine IsClosedUnderIsomorphisms.of_iso ?_ (AcyclicKerOfExactComplexAndBoundedFunctor F t₁ t₂
    S hexact hacy ha hb (k + 1) (l + 1) (by linarith))
  set e : S.sc l ≅ S.sc' k l (l + 1) :=
    S.isoSc' k l (l + 1) (by simp only [hkl.symm, CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next])
  have := ShortComplex.imageToKernelIsIsoOfExact (IsZero.of_iso
    ((S.exactAt_iff_isZero_homology _).mp (hexact l)) (ShortComplex.homologyMapIso e).symm)
  exact ((asIso (S.sc' k l (l + 1)).abelianImageToKernel).trans (kernel.mapIso (S.d l (l + 1))
    (S.d (k + 1) (l + 1)) (S.XIsoOfEq hkl.symm) (Iso.refl _)
    (by simp only [Iso.refl_hom, comp_id, HomologicalComplex.XIsoOfEq_hom_comp_d]))).symm

lemma AcyclicCoimageOfBoundedExactComplex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k l : ℤ) (hkl : k + 1 = l) :
    AcyclicObject F t₁ t₂ (Abelian.coimage (S.d k l)) :=
  IsClosedUnderIsomorphisms.of_iso (asIso (Abelian.coimageImageComparison (S.d k l))).symm
  (AcyclicImageOfBoundedExactComplex F t₁ t₂ S hexact hacy ha hb k l hkl)

lemma AcyclicCoimageOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k l : ℤ)
    (hkl : k + 1 = l) :
    AcyclicObject F t₁ t₂ (Abelian.coimage (S.d k l)) :=
  IsClosedUnderIsomorphisms.of_iso (asIso (Abelian.coimageImageComparison (S.d k l))).symm
  (AcyclicImageOfExactComplexAndBoundedFunctor F t₁ t₂ S hexact hacy ha hb k l hkl)

lemma AcyclicCokerOfBoundedExactComplex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k l : ℤ) (hkl : k + 1 = l) :
    AcyclicObject F t₁ t₂ (Limits.cokernel (S.d k l)) := by
  refine IsClosedUnderIsomorphisms.of_iso ?_ (AcyclicCoimageOfBoundedExactComplex F t₁ t₂ S hexact
    hacy ha hb (k + 1) (l + 1) (by linarith))
  set e : S.sc (k + 1) ≅ S.sc' k (k + 1) (l+ 1) :=
    S.isoSc' k (k + 1) (l + 1) (by simp only [CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next, hkl.symm])
  have := ShortComplex.cokernelToAbelianCoimageIsIsoOfExact (IsZero.of_iso
    ((S.exactAt_iff_isZero_homology _).mp (hexact (k + 1))) (ShortComplex.homologyMapIso e).symm)
  exact (asIso (S.sc' k (k + 1) (l + 1)).cokernelToAbelianCoimage).symm.trans
    (cokernel.mapIso (S.d k (k + 1)) (S.d k l) (Iso.refl _) (S.XIsoOfEq hkl)
    (by simp only [HomologicalComplex.d_comp_XIsoOfEq_hom, Iso.refl_hom, id_comp]))

lemma AcyclicCokerOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b: ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k l : ℤ)
    (hkl : k + 1 = l) :
    AcyclicObject F t₁ t₂ (Limits.cokernel (S.d k l)) := by
  refine IsClosedUnderIsomorphisms.of_iso ?_ (AcyclicCoimageOfExactComplexAndBoundedFunctor F t₁ t₂
    S hexact hacy ha hb (k + 1) (l + 1) (by linarith))
  set e : S.sc (k + 1) ≅ S.sc' k (k + 1) (l+ 1) :=
    S.isoSc' k (k + 1) (l + 1) (by simp only [CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next, hkl.symm])
  have := ShortComplex.cokernelToAbelianCoimageIsIsoOfExact (IsZero.of_iso
    ((S.exactAt_iff_isZero_homology _).mp (hexact (k + 1))) (ShortComplex.homologyMapIso e).symm)
  exact (asIso (S.sc' k (k + 1) (l + 1)).cokernelToAbelianCoimage).symm.trans
    (cokernel.mapIso (S.d k (k + 1)) (S.d k l) (Iso.refl _) (S.XIsoOfEq hkl)
    (by simp only [HomologicalComplex.d_comp_XIsoOfEq_hom, Iso.refl_hom, id_comp]))

noncomputable def LeftHomologyData_of_abelian_preserved (S : ShortComplex t₁.Heart)
    (he : S.Exact) (h₀ : AcyclicObject F t₁ t₂ (kernel S.f))
    (h₁ : AcyclicObject F t₁ t₂ (cokernel S.g)) (h₂ : AcyclicObject F t₁ t₂ (kernel S.g))
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image S.g)) :
    (ShortComplex.LeftHomologyData.ofAbelian S).IsPreservedBy (F.FromHeartToHeart t₁ t₂) where
  g := by
    have := IsIsoKernelComparisonOfAcyclic F t₁ t₂ S.g h₁ h₂ h₃
    exact PreservesKernel.of_iso_comparison _ _
  f' := by
    have := IsIsoCokernelComparisonOfAcyclic F t₁ t₂ (ShortComplex.LeftHomologyData.ofAbelian S).f'
      ?_ ?_ ?_
    · exact PreservesCokernel.of_iso_comparison _ _
    · exact IsClosedUnderIsomorphisms.of_iso S.homologyIsoCokernelLift (AcyclicCategory.zero F t₁ t₂
        (S.exact_iff_isZero_homology.mp he))
    · exact IsClosedUnderIsomorphisms.of_iso (S.LeftHomologyData_ker_f' _).symm h₀
    · refine IsClosedUnderIsomorphisms.of_iso (S.LeftHomologyData_image_f' _).symm ?_
      rw [S.exact_iff_isIso_abelianImageToKernel] at he
      exact IsClosedUnderIsomorphisms.of_iso (asIso S.abelianImageToKernel).symm h₂

noncomputable def PreservesLeftHomologyOfAcyclic (S : ShortComplex t₁.Heart)
    (he : S.Exact) (h₀ : AcyclicObject F t₁ t₂ (kernel S.f))
    (h₁ : AcyclicObject F t₁ t₂ (cokernel S.g)) (h₂ : AcyclicObject F t₁ t₂ (kernel S.g))
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image S.g)) :
    PreservesLeftHomologyOf (F.FromHeartToHeart t₁ t₂) S := by
  have := LeftHomologyData_of_abelian_preserved F t₁ t₂ S he h₀ h₁ h₂ h₃
  refine Functor.PreservesLeftHomologyOf.mk' (F.FromHeartToHeart t₁ t₂)
    (ShortComplex.LeftHomologyData.ofAbelian S)

namespace ShortComplex

omit [t₂.NonDegenerate] in
lemma MapExactOfExactAndAcyclic (S : ShortComplex t₁.Heart)
    (he : S.Exact) (h₀ : AcyclicObject F t₁ t₂ (kernel S.f))
    (h₁ : AcyclicObject F t₁ t₂ (cokernel S.g)) (h₂ : AcyclicObject F t₁ t₂ (kernel S.g))
    (h₃ : AcyclicObject F t₁ t₂ (Abelian.image S.g)) :
    (S.map (F.FromHeartToHeart t₁ t₂)).Exact := by
  have := PreservesLeftHomologyOfAcyclic F t₁ t₂ S he h₀ h₁ h₂ h₃
  exact he.map_of_preservesLeftHomologyOf _

end ShortComplex

namespace CochainComplex

lemma MapExactOfExactAndBoundedAcyclic (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (i : ℤ):
    (((F.FromHeartToHeart t₁ t₂).mapHomologicalComplex ((ComplexShape.up ℤ))).obj S).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  refine ShortComplex.MapExactOfExactAndAcyclic F t₁ t₂ (S.sc i) ?_ ?_ ?_ ?_ ?_
  · rw [← HomologicalComplex.exactAt_iff]; exact hexact i
  · simp only [HomologicalComplex.shortComplexFunctor_obj_X₁,
    HomologicalComplex.shortComplexFunctor_obj_X₂, HomologicalComplex.shortComplexFunctor_obj_f]
    exact AcyclicKerOfBoundedExactComplex F t₁ t₂ S hexact hacy ha hb _ i
      (by simp only [CochainComplex.prev, sub_add_cancel])
  · exact AcyclicCokerOfBoundedExactComplex F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])
  · exact AcyclicKerOfBoundedExactComplex F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])
  · exact AcyclicImageOfBoundedExactComplex F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])

lemma MapExactOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b: ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (i : ℤ) :
    (((F.FromHeartToHeart t₁ t₂).mapHomologicalComplex ((ComplexShape.up ℤ))).obj S).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  refine ShortComplex.MapExactOfExactAndAcyclic F t₁ t₂ (S.sc i) ?_ ?_ ?_ ?_ ?_
  · rw [← HomologicalComplex.exactAt_iff]; exact hexact i
  · simp only [HomologicalComplex.shortComplexFunctor_obj_X₁,
    HomologicalComplex.shortComplexFunctor_obj_X₂, HomologicalComplex.shortComplexFunctor_obj_f]
    exact AcyclicKerOfExactComplexAndBoundedFunctor F t₁ t₂ S hexact hacy ha hb _ i
      (by simp only [CochainComplex.prev, sub_add_cancel])
  · exact AcyclicCokerOfExactComplexAndBoundedFunctor F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])
  · exact AcyclicKerOfExactComplexAndBoundedFunctor F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])
  · exact AcyclicImageOfExactComplexAndBoundedFunctor F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])

end CochainComplex

end CategoryTheory
