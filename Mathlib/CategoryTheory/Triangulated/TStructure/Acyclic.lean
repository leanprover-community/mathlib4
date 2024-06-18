import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianCategoryLemmas
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

namespace CategoryTheory

open Category Limits Triangulated Pretriangulated TStructure

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

def FromAcyclicFactorization : F.FromAcyclic t₁ t₂ ≅
    fullSubcategoryInclusion (AcyclicObject F t₁ t₂) ⋙ F.FromHeartToHeart t₁ t₂ := sorry

end Functor

namespace AcyclicCategory

instance closedUnderIsomorphisms : ClosedUnderIsomorphisms (AcyclicObject F t₁ t₂) := by
  refine ClosedUnderIsomorphisms.mk ?_
  intro _ _ e hX
  change t₂.heart _
  exact ClosedUnderIsomorphisms.of_iso ((F.FromHeart t₁).mapIso e) hX

variable (X Y : t₁.Heart)

lemma zero {X : t₁.Heart} (hX : IsZero X) : AcyclicObject F t₁ t₂ X := by
  simp only [AcyclicObject]
  exact ClosedUnderIsomorphisms.of_iso (((F.FromHeart t₁).mapIso hX.isoZero).trans
    (F.FromHeart t₁).mapZeroObject).symm t₂.zero_mem_heart

lemma prod {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X) (hY : AcyclicObject F t₁ t₂ Y) :
    AcyclicObject F t₁ t₂ (X ⨯ Y) := by
  simp only [AcyclicObject]
  have := PreservesLimitPair.iso t₁.ιHeart X Y
  exact ClosedUnderIsomorphisms.of_iso (PreservesLimitPair.iso (F.FromHeart t₁) X Y).symm
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
  exact mem_of_iso (AcyclicObject F t₁ t₂)
    (limit.isoLimitCone ⟨_, (IsLimit.postcomposeHomEquiv (diagramIsoPair P) _).symm hc⟩)
    (prod F t₁ t₂ (H _) (H _))

instance : HasFiniteProducts (AcyclicCategory F t₁ t₂) :=
  hasFiniteProducts_of_has_binary_and_terminal

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

lemma ShortExactComplexToImageDistTriangle_distinguished {S : ShortComplex t₁.Heart}
    (he : S.ShortExact) : ShortExactComplexToImageDistTriangle F t₁ he ∈ distinguishedTriangles :=
  F.map_distinguished _ (heartShortExactTriangle_distinguished t₁ _ he)

noncomputable abbrev ShortExactComplexImageIsoHomology {S : ShortComplex t₁.Heart} (he : S.ShortExact) :
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

def IsIsoKernelComparisonOfEpi {X Y : t₁.Heart} (f : X ⟶ Y) (he : Epi f)
    (h₁ : AcyclicObject F t₁ t₂ (kernel f)) (h₃ : AcyclicObject F t₁ t₂ Y) :
    IsIso (kernelComparison f (F.FromHeartToHeart t₁ t₂)) := by
  rw [isIso_iff_mono_and_epi]
  set hx := ShortExactComplexImageShortExact' F t₁ t₂ (epiKernelComplexShortExact f he) h₁ h₃
  constructor
  · refine @mono_of_mono _ _ _ _ _ _ (kernel.ι ((F.FromHeartToHeart t₁ t₂).map f)) ?_
    rw [kernelComparison_comp_ι]
    exact hx.mono_f
  · set R₁ := (ShortComplex.mk ((F.FromHeartToHeart t₁ t₂).map (kernel.ι f))
      ((F.FromHeartToHeart t₁ t₂).map f)
      (by rw [← map_comp, kernel.condition, Functor.map_zero])).toComposableArrows
    set R₂ := (ShortComplex.mk (kernel.ι ((F.FromHeartToHeart t₁ t₂).map f))
      ((F.FromHeartToHeart t₁ t₂).map f) (kernel.condition _)).toComposableArrows
    have hR₁ : R₁.Exact := hx.exact.exact_toComposableArrows
    have hR₂ : R₂.Exact := (kernelComplexExact _).exact_toComposableArrows
    set φ : R₁ ⟶ R₂ := by
      refine ComposableArrows.homMk ?_ ?_
      · intro i
        match i with
        | 0 => exact kernelComparison f (F.FromHeartToHeart t₁ t₂)
        | 1 => exact 𝟙 _
        | 2 => exact 𝟙 _
      · intro i _
        match i with
        | 0 => erw [kernelComparison_comp_ι, comp_id]; rfl
        | 1 => erw [comp_id, id_comp]; rfl
    refine Abelian.epi_of_mono_of_epi_of_mono φ hR₁ hR₂ ?_ ?_ ?_
    · change Mono (kernel.ι _); exact inferInstance
    · change Epi (𝟙 _); exact inferInstance
    · change Mono (𝟙 _); exact inferInstance

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
      have := ClosedUnderIsomorphisms.of_iso this h₁
      simp only [AcyclicObject, mem_heart_iff] at this
      exact this.2
    · rw [← map_comp, Abelian.image.fac]
  · refine @normalEpiOfEpi (C := t₂.Heart) _ _ _ _ _ _  ?_
    refine EpiOfEpiAcyclicKernel F t₁ t₂ (Abelian.factorThruImage f) inferInstance
      (@isZero_homology_of_isLE _ _ _ _ _ _ _ t₂ _ _ _ _ _ (1 : ℤ) 0 zero_lt_one ?_)
    have := Limits.IsLimit.conePointUniqueUpToIso (kernelIsKernel f) (Limits.isKernelCompMono
      (kernelIsKernel (Abelian.factorThruImage f)) (Abelian.image.ι f) (Abelian.image.fac f).symm)
    have := ClosedUnderIsomorphisms.of_iso this h₂
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

--def IsIsoKernelComparisonOfAcyclic {X Y : t₁.Heart} (f : X ⟶ Y)

lemma AcyclicShortExact {S : ShortComplex (AcyclicCategory F t₁ t₂)}
    (SE : ((F.AcyclicToHeart t₁ t₂).mapShortComplex.obj S).ShortExact) :
    ((F.FromAcyclic t₁ t₂).mapShortComplex.obj S).ShortExact := by sorry
  -- prood needs to be adjusted because the definition of "Acyclic" changed
  /-
  set T := heartShortExactTriangle t₁ _ SE with hTdef
  set DT := heartShortExactTriangle_distinguished t₁ _ SE
  set T' := F.mapTriangle.obj T with hT'def
  set DT' := F.map_distinguished _ DT
  set X := T'.obj₁ with hXdef
  set Y := T'.obj₂ with hYdef
  set Z := T'.obj₃ with hZdef
  set hX : t₂.heart X := by
    simp only [hXdef, hT'def, hTdef, AcyclicToHeart, FullSubcategory.map, mapShortComplex_obj,
      mapTriangle_obj, id_eq, heartShortExactTriangle_obj₁, ιHeart, ShortComplex.map_X₁,
      heartShortExactTriangle_obj₂, ShortComplex.map_X₂, heartShortExactTriangle_obj₃,
      ShortComplex.map_X₃, heartShortExactTriangle_mor₁, ShortComplex.map_f,
      heartShortExactTriangle_mor₂, ShortComplex.map_g, heartShortExactTriangle_mor₃,
      Triangle.mk_obj₁]
    exact hS₁.2
  set hY : t₂.heart Y := by sorry
  set hZ : t₂.heart Z := by sorry
  set f : (⟨X, hX⟩ : t₂.Heart) ⟶ ⟨Y, hY⟩ := T'.mor₁ with hfdef
  set g : (⟨Y, hY⟩ : t₂.Heart) ⟶ ⟨Z, hZ⟩ := T'.mor₂ with hgdef
  set δ : t₂.ιHeart.obj (⟨Z, hZ⟩ : t₂.Heart) ⟶ (t₂.ιHeart.obj ⟨X, hX⟩)⟦1⟧ := T'.mor₃
  set h : Triangle.mk (t₂.ιHeart.map f) (t₂.ιHeart.map g) δ ∈ distinguishedTriangles := by
    refine isomorphic_distinguished T' DT' _ ?_
    refine Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [Triangle.mk_obj₁, hXdef, hT'def, hTdef, AcyclicToHeart, mapShortComplex_obj,
      mapTriangle_obj, id_eq, heartShortExactTriangle_obj₁, ShortComplex.map_X₁,
      heartShortExactTriangle_obj₂, ShortComplex.map_X₂, heartShortExactTriangle_obj₃,
      ShortComplex.map_X₃, heartShortExactTriangle_mor₁, ShortComplex.map_f,
      FullSubcategory.map_map, heartShortExactTriangle_mor₂, ShortComplex.map_g,
      heartShortExactTriangle_mor₃]
      exact Iso.refl (F.obj S.X₁.1)
    · simp only [Triangle.mk_obj₂, hYdef, hT'def, hTdef, AcyclicToHeart, mapShortComplex_obj,
      mapTriangle_obj, id_eq, heartShortExactTriangle_obj₁, ShortComplex.map_X₁,
      heartShortExactTriangle_obj₂, ShortComplex.map_X₂, heartShortExactTriangle_obj₃,
      ShortComplex.map_X₃, heartShortExactTriangle_mor₁, ShortComplex.map_f,
      FullSubcategory.map_map, heartShortExactTriangle_mor₂, ShortComplex.map_g,
      heartShortExactTriangle_mor₃]
      exact Iso.refl (F.obj S.X₂.1)
    · simp only [Triangle.mk_obj₃, hZdef, hT'def, hTdef, AcyclicToHeart, mapShortComplex_obj,
      mapTriangle_obj, id_eq, heartShortExactTriangle_obj₁, ShortComplex.map_X₁,
      heartShortExactTriangle_obj₂, ShortComplex.map_X₂, heartShortExactTriangle_obj₃,
      ShortComplex.map_X₃, heartShortExactTriangle_mor₁, ShortComplex.map_f,
      FullSubcategory.map_map, heartShortExactTriangle_mor₂, ShortComplex.map_g,
      heartShortExactTriangle_mor₃]
      exact Iso.refl (F.obj S.X₃.1)
    · simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, mapShortComplex_obj,
      mapTriangle_obj, heartShortExactTriangle_obj₁, ShortComplex.map_X₁,
      heartShortExactTriangle_obj₂, ShortComplex.map_X₂, heartShortExactTriangle_obj₃,
      ShortComplex.map_X₃, heartShortExactTriangle_mor₁, ShortComplex.map_f,
      heartShortExactTriangle_mor₂, ShortComplex.map_g, heartShortExactTriangle_mor₃,
      eq_mpr_eq_cast, cast_eq, Iso.refl_hom]
      erw [comp_id, id_comp]
      simp only [hfdef]; rfl
    · sorry -- same proof as first point, but with g
    · sorry -- same proof as first point, but with δ
  set e : (ShortComplex.mk f g (t₂.ιHeart.map_injective
    (by
      rw [Functor.map_comp, Functor.map_zero]
      exact comp_distTriang_mor_zero₁₂ _ h))) ≅
   ((mapShortComplex (FunctorFromAcyclic F t₁ t₂)).obj S) := by
    refine ShortComplex.isoMk ?_ ?_ ?_ ?_ ?_
    · refine (isoEquivOfFullyFaithful t₂.ιHeart).invFun ?_
      simp only [ιHeart, hXdef, hT'def, hTdef, AcyclicToHeart, FullSubcategory.map,
        mapShortComplex_obj, mapTriangle_obj, id_eq, heartShortExactTriangle_obj₁,
        ShortComplex.map_X₁, heartShortExactTriangle_obj₂, ShortComplex.map_X₂,
        heartShortExactTriangle_obj₃, ShortComplex.map_X₃, heartShortExactTriangle_mor₁,
        ShortComplex.map_f, heartShortExactTriangle_mor₂, ShortComplex.map_g,
        heartShortExactTriangle_mor₃, Triangle.mk_obj₁, FunctorFromAcyclic]
      exact Iso.refl (F.obj S.X₁.1)
    · refine (isoEquivOfFullyFaithful t₂.ιHeart).invFun ?_
      simp only [ιHeart, hYdef, hT'def, hTdef, AcyclicToHeart, FullSubcategory.map,
        mapShortComplex_obj, mapTriangle_obj, id_eq, heartShortExactTriangle_obj₁,
        ShortComplex.map_X₁, heartShortExactTriangle_obj₂, ShortComplex.map_X₂,
        heartShortExactTriangle_obj₃, ShortComplex.map_X₃, heartShortExactTriangle_mor₁,
        ShortComplex.map_f, heartShortExactTriangle_mor₂, ShortComplex.map_g,
        heartShortExactTriangle_mor₃, Triangle.mk_obj₁, FunctorFromAcyclic]
      exact Iso.refl (F.obj S.X₂.1)
    · refine (isoEquivOfFullyFaithful t₂.ιHeart).invFun ?_
      simp only [ιHeart, hZdef, hT'def, hTdef, AcyclicToHeart, FullSubcategory.map,
        mapShortComplex_obj, mapTriangle_obj, id_eq, heartShortExactTriangle_obj₁,
        ShortComplex.map_X₁, heartShortExactTriangle_obj₂, ShortComplex.map_X₂,
        heartShortExactTriangle_obj₃, ShortComplex.map_X₃, heartShortExactTriangle_mor₁,
        ShortComplex.map_f, heartShortExactTriangle_mor₂, ShortComplex.map_g,
        heartShortExactTriangle_mor₃, Triangle.mk_obj₁, FunctorFromAcyclic]
      exact Iso.refl (F.obj S.X₃.1)
    · simp only [id_eq, eq_mpr_eq_cast, cast_eq, FunctorFromAcyclic, mapShortComplex_obj,
      ShortComplex.map_X₂, ShortComplex.map_X₁, isoEquivOfFullyFaithful, mapTriangle_obj,
      heartShortExactTriangle_obj₁, heartShortExactTriangle_obj₂, heartShortExactTriangle_obj₃,
      ShortComplex.map_X₃, heartShortExactTriangle_mor₁, ShortComplex.map_f,
      heartShortExactTriangle_mor₂, ShortComplex.map_g, heartShortExactTriangle_mor₃,
      Triangle.mk_obj₁, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk, preimageIso_hom, Iso.refl_hom,
      FullSubcategory.lift_map, comp_map, fullSubcategoryInclusion.obj,
      fullSubcategoryInclusion.map, Triangle.mk_obj₂]
      refine t₂.ιHeart.map_injective ?_
      simp only [map_comp, image_preimage, hfdef]
      erw [comp_id, id_comp]
      congr 1
    · simp only [id_eq, eq_mpr_eq_cast, cast_eq, FunctorFromAcyclic, mapShortComplex_obj,
      ShortComplex.map_X₂, ShortComplex.map_X₁, isoEquivOfFullyFaithful, mapTriangle_obj,
      heartShortExactTriangle_obj₁, heartShortExactTriangle_obj₂, heartShortExactTriangle_obj₃,
      ShortComplex.map_X₃, heartShortExactTriangle_mor₁, ShortComplex.map_f,
      heartShortExactTriangle_mor₂, ShortComplex.map_g, heartShortExactTriangle_mor₃,
      Triangle.mk_obj₁, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk, preimageIso_hom, Iso.refl_hom,
      FullSubcategory.lift_map, comp_map, fullSubcategoryInclusion.obj,
      fullSubcategoryInclusion.map, Triangle.mk_obj₂]
      refine t₂.ιHeart.map_injective ?_
      simp only [map_comp, image_preimage, hgdef]
      erw [comp_id, id_comp]
      congr 1
  exact ShortComplex.shortExact_of_iso e (shortExact_of_distTriang t₂ δ h)
-/


noncomputable def ShortComplexHomologyFunctor (S : ShortComplex t₁.Heart)
    (hS₁ : AcyclicObject F t₁ t₂ S.X₁) (hS : S.Exact) {n : ℤ} (hn : n ≠ -1 ∧ n ≠ 0) :
    (t₂.homology n).obj (F.obj (Limits.kernel S.g).1) ≅ (t₂.homology (n + 1)).obj
    (F.obj (Limits.kernel S.f).1) := by sorry
/-  set S' : ShortComplex t₁.Heart := ShortComplex.mk (X₁ := Limits.kernel S.f) (X₂ := S.X₁)
    (X₃ := Limits.kernel S.g) (Limits.kernel.ι S.f) (Limits.kernel.lift S.g S.f S.zero)
    (by refine Mono.right_cancellation (f := Limits.kernel.ι S.g) _ _ ?_
        simp only [assoc, kernel.lift_ι, kernel.condition, zero_comp])
    with hS'def
  set S'' : ShortComplex t₁.Heart := ShortComplex.mk (Limits.kernel.ι S.f)
    (Abelian.factorThruImage S.f) (by
    refine Mono.right_cancellation (f := Abelian.image.ι S.f) _ _ ?_
    simp only [equalizer_as_kernel, assoc, kernel.lift_ι, kernel.condition, zero_comp])
    with hS''def
  rw [← exact_iff_shortComplex_exact] at hS
  set e : S' ≅ S'' := by
    refine ShortComplex.isoMk (Iso.refl (Limits.kernel S.f)) (Iso.refl S.X₁)
      (Limits.IsLimit.conePointUniqueUpToIso (Limits.kernelIsKernel S.g)
      (Abelian.isLimitImage S.f S.g hS)) (by simp only [Iso.refl_hom, id_comp, comp_id]) ?_
    refine Mono.right_cancellation (f := Abelian.image.ι S.f) _ _ ?_
    simp only [Iso.refl_hom, id_comp, equalizer_as_kernel, kernel.lift_ι, coequalizer_as_cokernel,
        eq_mp_eq_cast, IsLimit.lift_comp_conePointUniqueUpToIso_hom]
    have := (Abelian.isLimitImage S.f S.g hS).fac (KernelFork.ofι S.f S.zero)
        Limits.WalkingParallelPair.zero
    simp only [Fork.ofι_pt, parallelPair_obj_zero, equalizer_as_kernel, coequalizer_as_cokernel,
        Fork.ofι_π_app] at this
    exact this.symm
  have hS' : S'.ShortExact := by
    refine ShortComplex.shortExact_of_iso e.symm (ShortComplex.ShortExact.mk' ?_ ?_ ?_)
    · rw [← exact_iff_shortComplex_exact, ← exact_comp_mono_iff (h := Abelian.image.ι S.f)]
      simp only [equalizer_as_kernel, kernel.lift_ι]
      rw [Abelian.exact_iff]
      aesop_cat
    · exact inferInstance
    · exact inferInstance
  set T := t₁.heartShortExactTriangle S' hS'
  have hT := t₁.heartShortExactTriangle_distinguished S' hS'
  have hT' := F.map_distinguished T hT
  set f := t₂.homologyδ (F.mapTriangle.obj T) n (n + 1) rfl
  have h1 : Mono f := by
    refine (ShortComplex.exact_iff_mono _ (Limits.zero_of_source_iso_zero _ ?_)).mp
      (t₂.homology_exact₃ _ hT' n (n + 1) rfl)
    change (t₂.homology n).obj (F.obj S.X₁.1) ≅ 0
    refine Limits.IsZero.isoZero ?_
    by_cases hn' : 0 ≤ n
    · letI : t₂.IsLE (F.obj S.X₁.1) 0 := {le := hS₁.1}
      exact t₂.isZero_homology_of_isLE _ n 0 (lt_iff_le_and_ne.mpr ⟨hn', Ne.symm hn.2⟩)
    · letI : t₂.IsGE (F.obj S.X₁.1) 0 := {ge := hS₁.2}
      exact t₂.isZero_homology_of_isGE _ n 0 (lt_iff_not_le.mpr hn')
  have h2 : Epi f := by
    refine (ShortComplex.exact_iff_epi _ (Limits.zero_of_target_iso_zero _ ?_)).mp
      (t₂.homology_exact₁ _ hT' n (n + 1) rfl)
    change (t₂.homology (n + 1)).obj (F.obj S.X₁.1) ≅ 0
    refine Limits.IsZero.isoZero ?_
    by_cases hn' : 0 ≤ n
    · letI : t₂.IsLE (F.obj S.X₁.1) 0 := {le := hS₁.1}
      exact t₂.isZero_homology_of_isLE _ (n + 1) 0 (Int.lt_add_one_iff.mpr hn')
    · letI : t₂.IsGE (F.obj S.X₁.1) 0 := {ge := hS₁.2}
      refine t₂.isZero_homology_of_isGE _ (n + 1) 0 ?_
      rw [lt_iff_le_and_ne, Int.add_one_le_iff, and_iff_right (lt_iff_not_le.mpr hn'), ne_eq,
          ← eq_neg_iff_add_eq_zero]
      exact hn.1
  exact @asIso _ _ _ _ f ((isIso_iff_mono_and_epi f).mpr ⟨h1, h2⟩)-/

noncomputable def KernelMapEpiAcyclic {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X)
    (hY : AcyclicObject F t₁ t₂ Y) (f : X ⟶ Y)
    (hf1 : AcyclicObject F t₁ t₂ (Limits.kernel f)) (hf2 : Epi f)
    {c : KernelFork f} (hc : IsLimit c) :
    IsLimit ((F.FromHeartToHeart t₁ t₂).mapKernelFork c) := by sorry
/-  refine IsLimit.ofIsoLimit (r := Limits.KernelFork.ofι (f := (F.FromHeartToHeart t₁ t₂).map
     f) ((F.FromHeartToHeart t₁ t₂).map (kernel.ι f))
    (by rw [← map_comp, kernel.condition, Functor.map_zero])) ?_ ?_
  · set Z : AcyclicCategory F t₁ t₂ := ⟨(Limits.kernel f), hf1⟩
    set g : Z ⟶ ⟨X, hX⟩ := Limits.kernel.ι f with hgdef
    set f' : (⟨X, hX⟩ : AcyclicCategory F t₁ t₂) ⟶ ⟨Y, hY⟩ := f with hf'def
    set S := ShortComplex.mk (C := AcyclicCategory F t₁ t₂) g f'
      (by refine Functor.Faithful.map_injective (F := fullSubcategoryInclusion _) ?_
          simp only [fullSubcategoryInclusion.obj, hgdef, hf'def, fullSubcategoryInclusion.map]
          exact kernel.condition f (C := t₁.Heart))
    have SE : ((AcyclicToHeart F t₁ t₂).mapShortComplex.obj S).ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · refine ShortComplex.exact_of_f_is_kernel _ ?_
        simp only [AcyclicToHeart, fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map, id_eq,
          eq_mpr_eq_cast, cast_eq, mapShortComplex_obj, ShortComplex.map_X₂, ShortComplex.map_X₃,
          ShortComplex.map_g, ShortComplex.map_X₁, ShortComplex.map_f, S, g]
        exact kernelIsKernel _
      · simp only [fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map, id_eq, eq_mpr_eq_cast,
        cast_eq, mapShortComplex_obj, ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_f, S]
        change Mono (Limits.kernel.ι (C := t₁.Heart) f)
        exact inferInstance
      · simp only [fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map, id_eq, eq_mpr_eq_cast,
        cast_eq, mapShortComplex_obj, ShortComplex.map_X₂, ShortComplex.map_X₃, ShortComplex.map_g, S]
        simp only [f', AcyclicToHeart]; change Epi (C := t₁.Heart) f
        exact hf2
    have FSE : ((FunctorFromAcyclic F t₁ t₂).mapShortComplex.obj S).ShortExact :=
      AcyclicShortExact F t₁ t₂ SE
    set S' := (F.FromHeartToHeart t₁ t₂).mapShortComplex.obj
      (ShortComplex.mk (kernel.ι (C := t₁.Heart) f) f (kernel.condition (C := t₁.Heart) f)) with hS'
    have S'E : S'.ShortExact := by
      refine ShortComplex.shortExact_of_iso ((ShortComplex.mapNatIso _
        (FunctorFromAcyclicFactorization F t₁ t₂)).trans ?_ ) FSE
      simp only [hS', mapShortComplex_obj]
      refine ShortComplex.isoMk ?_ ?_ ?_ ?_ ?_
      · simp only [ShortComplex.map_X₁, comp_obj, fullSubcategoryInclusion.obj]
        exact Iso.refl _
      · simp only [ShortComplex.map_X₂, comp_obj, fullSubcategoryInclusion.obj]
        exact Iso.refl _
      · simp only [ShortComplex.map_X₃, comp_obj, fullSubcategoryInclusion.obj]
        exact Iso.refl _
      · simp only [ShortComplex.map_X₁, comp_obj, fullSubcategoryInclusion.obj, ShortComplex.map_X₂,
        id_eq, Iso.refl_hom, ShortComplex.map_f, comp_map, id_comp, fullSubcategoryInclusion.map,
        comp_id]
      · simp only [ShortComplex.map_X₂, comp_obj, fullSubcategoryInclusion.obj, ShortComplex.map_X₃,
        id_eq, Iso.refl_hom, ShortComplex.map_g, comp_map, id_comp, fullSubcategoryInclusion.map,
        comp_id]
    exact ShortComplex.ShortExact.fIsKernel S'E
  · refine (((F.FromHeartToHeart t₁ t₂).mapKernelForkIso c).trans ?_).symm
    refine Cones.ext ?_ ?_
    · simp only [const_obj_obj, Fork.ofι_pt]
      have := (F.FromHeartToHeart t₁ t₂).mapIso (IsLimit.conePointUniqueUpToIso hc
        (kernelIsKernel f))
      exact this
    · intro j
      cases j with
      | zero => simp only [const_obj_obj, parallelPair_obj_zero, Fork.ofι_pt, Fork.ofι_π_app,
         id_eq, eq_mpr_eq_cast, mapIso_hom]
                erw [← map_comp]
                refine congrArg _ ?_
                simp only [const_obj_obj, parallelPair_obj_zero]
                change c.π.app _ = _
                rw [← IsLimit.conePointUniqueUpToIso_hom_comp hc (kernelIsKernel f)]
                simp only [const_obj_obj, parallelPair_obj_zero, Fork.ofι_pt, Fork.ofι_π_app]
      | one => simp only [const_obj_obj, parallelPair_obj_zero, Fork.ofι_pt, parallelPair_obj_one,
         Fork.ofι_π_app, id_eq, eq_mpr_eq_cast, mapIso_hom]
               erw [← Functor.map_comp, ← map_comp, ← map_comp]
               refine congrArg _ ?_
               simp only [KernelFork.condition, kernel.condition, comp_zero]-/

--set_option maxHeartbeats 500000

noncomputable def KernelMapAcyclic {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X)
    (hY : AcyclicObject F t₁ t₂ Y)
    (f : X ⟶ Y) (hf0 : AcyclicObject F t₁ t₂ (Abelian.image f))
    (hf1 : AcyclicObject F t₁ t₂ (Limits.kernel f))
    (hf2 : AcyclicObject F t₁ t₂ (Limits.cokernel f)) {c : KernelFork f} (hc : IsLimit c) :
    IsLimit ((F.FromHeartToHeart t₁ t₂).mapKernelFork c) := by sorry
/-  set g := Abelian.factorThruImage f
  have hg := isKernelCompMono (kernelIsKernel g) (Abelian.image.ι f)
    (Abelian.image.fac f).symm
  have hg1 : AcyclicObject F t₁ t₂ (kernel g) := by
    set e := IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hg
    exact ClosedUnderIsomorphisms.of_iso e hf1
  set hgK := KernelMapEpiAcyclic F t₁ t₂ hX hf0 g hg1 inferInstance (kernelIsKernel g)
  have heq : (F.FromHeartToHeart t₁ t₂).map f =
      (F.FromHeartToHeart t₁ t₂).map g ≫ (F.FromHeartToHeart t₁ t₂).map
      (Abelian.image.ι f) := by rw [← map_comp, Abelian.image.fac]
  have hgK' := IsLimit.ofIsoLimit hgK ((F.FromHeartToHeart t₁ t₂).mapKernelForkIso
    (KernelFork.ofι (kernel.ι g) (kernel.condition g)))
  have hmon : Mono ((F.FromHeartToHeart t₁ t₂).map (Abelian.image.ι f)) := by
    have : IsLimit (Fork.ofι (Abelian.image.ι f) (by simp only [equalizer_as_kernel,
      kernel.condition, comp_zero])) :=
      kernelIsKernel (cokernel.π f)
    have := KernelMapEpiAcyclic F t₁ t₂ hY hf2 (cokernel.π f) hf0 inferInstance this
    set e := (F.FromHeartToHeart t₁ t₂).mapKernelForkIso (KernelFork.ofι
      (Abelian.image.ι f) (f := cokernel.π f) (by simp only [equalizer_as_kernel,
        kernel.condition]))
    have := IsLimit.ofIsoLimit this e
    simp only [equalizer_as_kernel, Fork.ofι_pt, const_obj_obj, Fork.ι_ofι] at this
    have := mono_of_isLimit_fork this
    simp only [equalizer_as_kernel, Fork.ofι_pt, const_obj_obj, Fork.ι_ofι,
      parallelPair_obj_zero, id_eq] at this
    exact this
  letI := hmon
  have := isKernelCompMono hgK' ((F.FromHeartToHeart t₁ t₂).map (Abelian.image.ι f)) heq
  simp only [Fork.ofι_pt, const_obj_obj, Fork.ι_ofι, parallelPair_obj_zero] at this
  set e := (KernelFork.functoriality (F.FromHeartToHeart t₁ t₂) _).mapIso
    (IsLimit.uniqueUpToIso hg hc)
  simp only [comp_obj, comp_map, KernelFork.functoriality, eq_mpr_eq_cast, cast_eq, id_eq,
    Fork.ofι_pt, const_obj_obj, Fork.ι_ofι] at e
  set f := ((F.FromHeartToHeart t₁ t₂).mapKernelForkIso (KernelFork.ofι (kernel.ι g)
    (f := f) (by conv_lhs => congr; simp only [g]; rfl; rw [← Abelian.image.fac f]
                 rw [← Category.assoc, kernel.condition, zero_comp])))
  exact IsLimit.ofIsoLimit this (f.symm.trans e)-/


noncomputable def preservesKernelOfAcyclic {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X)
    (hY : AcyclicObject F t₁ t₂ Y)
    (f : X ⟶ Y) (hf0 : AcyclicObject F t₁ t₂ (Abelian.image f))
    (hf1 : AcyclicObject F t₁ t₂ (Limits.kernel f))
    (hf2 : AcyclicObject F t₁ t₂ (Limits.cokernel f)) :
    PreservesLimit (parallelPair f 0) (F.FromHeartToHeart t₁ t₂) where
  preserves := by
    intro c limc
    have := KernelMapAcyclic F t₁ t₂ hX hY f hf0 hf1 hf2 limc
    simp only [comp_obj, Functor.comp_map, mapKernelFork] at this
    exact (IsLimit.postcomposeHomEquiv (compNatIso' (F.FromHeartToHeart t₁ t₂))
      ((F.FromHeartToHeart t₁ t₂).mapCone c)).toFun this

noncomputable def kernelComparisonIsIso {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X)
    (hY : AcyclicObject F t₁ t₂ Y)
    (f : X ⟶ Y) (hf0 : AcyclicObject F t₁ t₂ (Abelian.image f))
    (hf1 : AcyclicObject F t₁ t₂ (Limits.kernel f))
    (hf2 : AcyclicObject F t₁ t₂ (Limits.cokernel f)) :
    IsIso (kernelComparison f (F.FromHeartToHeart t₁ t₂)) :=
  @instIsIsoKernelComparison _ _ _ _ _ _ (F.FromHeartToHeart t₁ t₂) _ _ _ f _ _
  (preservesKernelOfAcyclic F t₁ t₂ hX hY f hf0 hf1 hf2)

/- Dual results, sorried for now.-/

noncomputable def CokernelMapAcyclic {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X)
    (hY : AcyclicObject F t₁ t₂ Y)
    (f : X ⟶ Y) (hf0 : AcyclicObject F t₁ t₂ (Abelian.image f))
    (hf1 : AcyclicObject F t₁ t₂ (Limits.kernel f))
    (hf2 : AcyclicObject F t₁ t₂ (Limits.cokernel f)) {c : CokernelCofork f} (hc : IsColimit c) :
    IsColimit ((F.FromHeartToHeart t₁ t₂).mapCokernelCofork c) := by sorry

noncomputable def preservesCokernelOfAcyclic {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X)
    (hY : AcyclicObject F t₁ t₂ Y)
    (f : X ⟶ Y) (hf0 : AcyclicObject F t₁ t₂ (Abelian.image f))
    (hf1 : AcyclicObject F t₁ t₂ (Limits.kernel f))
    (hf2 : AcyclicObject F t₁ t₂ (Limits.cokernel f)) :
    PreservesColimit (parallelPair f 0) (F.FromHeartToHeart t₁ t₂) where
  preserves := by
    intro c limc
    have := CokernelMapAcyclic F t₁ t₂ hX hY f hf0 hf1 hf2 limc
    simp only [comp_obj, Functor.comp_map, mapCokernelCofork] at this
    sorry

noncomputable def cokernelComparisonIsIso {X Y : t₁.Heart} (hX : AcyclicObject F t₁ t₂ X)
    (hY : AcyclicObject F t₁ t₂ Y)
    (f : X ⟶ Y) (hf0 : AcyclicObject F t₁ t₂ (Abelian.image f))
    (hf1 : AcyclicObject F t₁ t₂ (Limits.kernel f))
    (hf2 : AcyclicObject F t₁ t₂ (Limits.cokernel f)) :
    IsIso (cokernelComparison f (F.FromHeartToHeart t₁ t₂)) :=
  @instIsIsoCokernelComparison _ _ _ _ _ _ (F.FromHeartToHeart t₁ t₂) _ _ _ f _ _
  (preservesCokernelOfAcyclic F t₁ t₂ hX hY f hf0 hf1 hf2)

noncomputable def RightAcyclicKer_aux (S : CochainComplex t₁.Heart ℤ) {r k : ℤ}
    (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → IsZero (S.homology i))
    (hk2 : ∀ (i : ℤ), i ≤ k → AcyclicObject F t₁ t₂ (S.X i)) (n : ℕ) :
    (t₂.homology r).obj (F.obj (Limits.kernel (S.d k (k + 1))).1) ≅ (t₂.homology (r + n)).obj
    (F.obj (Limits.kernel (S.d (k - n) (k - n + 1))).1) := by
  induction' n with n hn
  · simp only [CharP.cast_eq_zero, add_zero, Int.Nat.cast_ofNat_Int]
    erw [sub_zero]
  · have : r + ↑(n + 1) = (r + n) + 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [this]
    have : k - ↑(n + 1) = (k - n) - 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [this]
    have : k - n - 1 + 1 = k - n := by ring
    rw [this]
    refine hn.trans ?_
    set e := ShortComplexHomologyFunctor F t₁ t₂ (S.sc (k - n))
      (by simp only [HomologicalComplex.shortComplexFunctor_obj_X₁, CochainComplex.prev]
          exact hk2 (k - n - 1) (by linarith))
      (by rw [ShortComplex.exact_iff_isZero_homology]; exact hk1 (k - n) (by linarith))
      (n := r + n) ⟨by linarith [hr], by linarith [hr]⟩
    simp only [HomologicalComplex.shortComplexFunctor_obj_X₂,
      HomologicalComplex.shortComplexFunctor_obj_X₃, HomologicalComplex.shortComplexFunctor_obj_g,
      HomologicalComplex.shortComplexFunctor_obj_X₁,
      HomologicalComplex.shortComplexFunctor_obj_f] at e
    have : ((ComplexShape.up ℤ).prev (k - ↑n)) = k - n - 1 := by
      simp only [CochainComplex.prev]
    rw [← this]
    have : ((ComplexShape.up ℤ).next (k - ↑n)) = k - n + 1 := by
      simp only [CochainComplex.next]
    rw [← this]
    exact e

lemma RightAcyclicKerOfBoundedComplex (S : CochainComplex t₁.Heart ℤ) {r k : ℤ}
    (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → IsZero (S.homology i))
    (hk2 : ∀ (i : ℤ), i ≤ k → AcyclicObject F t₁ t₂ (S.X i)) {a : ℤ}
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j)) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k (k + 1))).1)) := by
  refine IsZero.of_iso ?_ (RightAcyclicKer_aux F t₁ t₂ S hr hk1 hk2 (k - a).natAbs)
  suffices h : IsZero (kernel (S.d (k - ↑(k - a).natAbs) (k - ↑(k - a).natAbs + 1))) by
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    change IsZero ((fullSubcategoryInclusion _).obj _)
    refine Functor.map_isZero _ h
  refine IsZero.of_mono (kernel.ι (S.d (k - (k - a).natAbs) (k - (k - a).natAbs + 1))) (ha _ ?_)
  rw [tsub_le_iff_right, ← tsub_le_iff_left]; exact Int.le_natAbs

lemma RightAcyclicKerOfBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {r k : ℤ}
    (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → IsZero (S.homology i))
    (hk2 : ∀ (i : ℤ), i ≤ k → AcyclicObject F t₁ t₂ (S.X i)) {d : ℤ}
    (hd : ∀ (X : t₁.Heart) (j : ℤ), d ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k (k + 1))).1)) := by
  refine IsZero.of_iso (hd _ _ ?_) (RightAcyclicKer_aux F t₁ t₂ S hr hk1 hk2 (d - r).natAbs)
  rw [← tsub_le_iff_left]; exact Int.le_natAbs

noncomputable def LeftAcyclicKer_aux (S : CochainComplex t₁.Heart ℤ) {r k : ℤ}
    (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → IsZero (S.homology i))
    (hk2 : ∀ (i : ℤ), k ≤ i → AcyclicObject F t₁ t₂ (S.X i)) (n : ℕ) :
    (t₂.homology r).obj (F.obj (Limits.kernel (S.d k (k + 1))).1) ≅ (t₂.homology (r - n)).obj
    (F.obj (Limits.kernel (S.d (k + n) (k + n + 1))).1) := by
  induction' n with n hn
  · simp only [CharP.cast_eq_zero, sub_zero, Int.Nat.cast_ofNat_Int]
    erw [add_zero]
  · refine hn.trans ?_
    have : r - (n + 1) = r - n - 1 := by ring
    erw [this]
    set e := ShortComplexHomologyFunctor F t₁ t₂ (S.sc (k + (n + 1)))
      (by simp only [HomologicalComplex.shortComplexFunctor_obj_X₁, CochainComplex.prev]
          refine hk2 _ (by linarith))
      (by rw [ShortComplex.exact_iff_isZero_homology]; exact hk1 _ (by linarith))
      (n := r - n - 1) ⟨by linarith [hr], by linarith [hr]⟩
    simp only [HomologicalComplex.shortComplexFunctor_obj_X₂,
      HomologicalComplex.shortComplexFunctor_obj_X₃, HomologicalComplex.shortComplexFunctor_obj_g,
      sub_add_cancel, HomologicalComplex.shortComplexFunctor_obj_X₁,
      HomologicalComplex.shortComplexFunctor_obj_f] at e
    have : ((ComplexShape.up ℤ).prev (k + (n + 1))) = k + n := by
      simp only [CochainComplex.prev]; ring
    rw [add_assoc, ← this]
    have : ((ComplexShape.up ℤ).next (k + (n + 1))) = k + (n + 1) + 1 := by
      simp only [CochainComplex.next]
    erw [← this]
    exact e.symm

lemma LeftAcyclicKerOfBoundedComplex (S : CochainComplex t₁.Heart ℤ) {r k : ℤ}
    (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → IsZero (S.homology i))
    (hk2 : ∀ (i : ℤ), k ≤ i → AcyclicObject F t₁ t₂ (S.X i)) {b : ℤ}
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k (k + 1))).1)) := by
  refine IsZero.of_iso ?_ (LeftAcyclicKer_aux F t₁ t₂ S hr hk1 hk2 (b - k).natAbs)
  suffices h : IsZero (kernel (S.d (k + ↑(b - k).natAbs) (k + ↑(b - k).natAbs + 1))) by
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    change IsZero ((fullSubcategoryInclusion _).obj _)
    refine Functor.map_isZero _ h
  refine IsZero.of_mono (kernel.ι (S.d (k + (b - k).natAbs) (k + (b - k).natAbs + 1))) (hb _ ?_)
  rw [← tsub_le_iff_left]; exact Int.le_natAbs

lemma LeftAcyclicKerOfBoundedFunctor (S : CochainComplex t₁.Heart ℤ){r k : ℤ}
    (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → IsZero (S.homology i))
    (hk2 : ∀ (i : ℤ), k ≤ i → AcyclicObject F t₁ t₂ (S.X i)) {c : ℤ}
    (hc : ∀ (X : t₁.Heart) (j : ℤ), j ≤ c → IsZero ((t₂.homology j).obj (F.obj X.1))) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k (k + 1))).1)) := by
  refine IsZero.of_iso (hc _ _ ?_) (LeftAcyclicKer_aux F t₁ t₂ S hr hk1 hk2 (r - c).natAbs)
  rw [tsub_le_iff_left, ← tsub_le_iff_right]; exact Int.le_natAbs

variable [NonDegenerate t₂]

lemma AcyclicKerOfBoundedExactComplex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), IsZero (S.homology i))
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k : ℤ) :
    AcyclicObject F t₁ t₂ (Limits.kernel (S.d k (k + 1))) := by
  simp only [AcyclicObject]
  refine isHeart_of_isZero_homology t₂ _ ?_
  intro j hj
  rw [ne_iff_lt_or_gt] at hj
  cases hj with
  | inl h => exact LeftAcyclicKerOfBoundedComplex F t₁ t₂ S h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) hb
  | inr h => exact RightAcyclicKerOfBoundedComplex F t₁ t₂ S h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) ha

lemma AcyclicKerOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b: ℤ}
    (hexact : ∀ (i : ℤ), IsZero (S.homology i))
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (k : ℤ) :
    AcyclicObject F t₁ t₂ (Limits.kernel (S.d k (k + 1))) := by
  simp only [AcyclicObject]
  refine isHeart_of_isZero_homology t₂ _ ?_
  intro j hj
  rw [ne_iff_lt_or_gt] at hj
  cases hj with
  | inl h => exact LeftAcyclicKerOfBoundedFunctor F t₁ t₂ S h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) ha
  | inr h => exact RightAcyclicKerOfBoundedFunctor F t₁ t₂ S h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) hb

lemma AcyclicImageOfBoundedExactComplex (S : CochainComplex t₁.Heart ℤ) {a b: ℤ}
    (hexact : ∀ (i : ℤ), IsZero (S.homology i))
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k : ℤ) :
    AcyclicObject F t₁ t₂ (Abelian.image (S.d k (k + 1))) := by
  refine ClosedUnderIsomorphisms.of_iso ?_ (AcyclicKerOfBoundedExactComplex F t₁ t₂ S hexact
    hacy ha hb (k + 1))
  set e : S.sc (k + 1) ≅ S.sc' k (k + 1) (k + 1 + 1) :=
    S.isoSc' k (k + 1) (k + 1 + 1) (by simp only [CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next])
  have := ShortComplex.imageToKernelIsIsoOfExact (IsZero.of_iso (hexact (k + 1))
    (ShortComplex.homologyMapIso e).symm)
  exact (asIso (S.sc' k (k + 1) (k + 1 + 1)).abelianImageToKernel).symm

lemma AcyclicImageOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), IsZero (S.homology i))
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k : ℤ) :
    AcyclicObject F t₁ t₂ (Abelian.image (S.d k (k + 1))) := by
  refine ClosedUnderIsomorphisms.of_iso ?_ (AcyclicKerOfExactComplexAndBoundedFunctor F t₁ t₂
    S hexact hacy ha hb (k + 1))
  set e : S.sc (k + 1) ≅ S.sc' k (k + 1) (k + 1 + 1) :=
    S.isoSc' k (k + 1) (k + 1 + 1) (by simp only [CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next])
  have := ShortComplex.imageToKernelIsIsoOfExact (IsZero.of_iso (hexact (k + 1))
    (ShortComplex.homologyMapIso e).symm)
  exact (asIso (S.sc' k (k + 1) (k + 1 + 1)).abelianImageToKernel).symm

lemma AcyclicCoimageOfBoundedExactComplex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), IsZero (S.homology i))
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k : ℤ) :
    AcyclicObject F t₁ t₂ (Abelian.coimage (S.d k (k + 1))) :=
  ClosedUnderIsomorphisms.of_iso (asIso (Abelian.coimageImageComparison (S.d k (k + 1)))).symm
  (AcyclicImageOfBoundedExactComplex F t₁ t₂ S hexact hacy ha hb k)

lemma AcyclicCoimageOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), IsZero (S.homology i))
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k : ℤ) :
    AcyclicObject F t₁ t₂ (Abelian.coimage (S.d k (k + 1))) :=
  ClosedUnderIsomorphisms.of_iso (asIso (Abelian.coimageImageComparison (S.d k (k + 1)))).symm
  (AcyclicImageOfExactComplexAndBoundedFunctor F t₁ t₂ S hexact hacy ha hb k)

lemma AcyclicCokerOfBoundedExactComplex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), IsZero (S.homology i))
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k : ℤ) :
    AcyclicObject F t₁ t₂ (Limits.cokernel (S.d k (k + 1))) := by
  refine ClosedUnderIsomorphisms.of_iso ?_ (AcyclicCoimageOfBoundedExactComplex F t₁ t₂ S hexact
    hacy ha hb (k + 1))
  set e : S.sc (k + 1) ≅ S.sc' k (k + 1) (k + 1 + 1) :=
    S.isoSc' k (k + 1) (k + 1 + 1) (by simp only [CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next])
  have := ShortComplex.cokernelToAbelianCoimageIsIsoOfExact (IsZero.of_iso (hexact (k + 1))
    (ShortComplex.homologyMapIso e).symm)
  exact (asIso (S.sc' k (k + 1) (k + 1 + 1)).cokernelToAbelianCoimage).symm

lemma AcyclicCokerOfExactComplexAndBoundedFunctor (S : CochainComplex t₁.Heart ℤ) {a b: ℤ}
    (hexact : ∀ (i : ℤ), IsZero (S.homology i))
    (hacy : ∀ (i : ℤ), AcyclicObject F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k : ℤ) :
    AcyclicObject F t₁ t₂ (Limits.cokernel (S.d k (k + 1))) := by
  refine ClosedUnderIsomorphisms.of_iso ?_ (AcyclicCoimageOfExactComplexAndBoundedFunctor F t₁ t₂
    S hexact hacy ha hb (k + 1))
  set e : S.sc (k + 1) ≅ S.sc' k (k + 1) (k + 1 + 1) :=
    S.isoSc' k (k + 1) (k + 1 + 1) (by simp only [CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next])
  have := ShortComplex.cokernelToAbelianCoimageIsIsoOfExact (IsZero.of_iso (hexact (k + 1))
    (ShortComplex.homologyMapIso e).symm)
  exact (asIso (S.sc' k (k + 1) (k + 1 + 1)).cokernelToAbelianCoimage).symm



#exit

lemma ExactOfExactComplex {a b : ℤ} (hb : IsCohomologicalBound F t₁ t₂ a b)
    {S : CochainComplex t₁.Heart ℤ} (Sexact : ∀ (n : ℤ), S.homology n = 0) :
    0 = 0 := sorry
