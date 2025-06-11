import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianCategoryLemmas
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

namespace CategoryTheory

open Category Limits Triangulated Pretriangulated TStructure ObjectProperty

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

scoped [ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.zero'

open ZeroObject Limits Preadditive Pretriangulated CategoryTheory.Functor

variable (F : C ⥤ D) (t₁ : TStructure C) (t₂ : TStructure D)

local instance : t₁.HasHeart := hasHeartFullSubcategory t₁
local instance : t₂.HasHeart := hasHeartFullSubcategory t₂

/--
An object of `t₁.heart` is called `F`-acyclic if its image by `F` is concentrated in degree
`0` (for `t₂`).
-/
def Acyclic : ObjectProperty t₁.Heart := fun X ↦ t₂.heart (F.obj X.1)

namespace Functor

/--
The functor induced by `F` from the full subcategort of acyclic objects of `t₁.heart` to `t₂.heart`.
-/
abbrev fromAcyclic : (Acyclic F t₁ t₂).FullSubcategory ⥤ t₂.Heart := by
  refine t₂.heart.lift ((Acyclic F t₁ t₂).ι ⋙ t₁.ιHeart ⋙ F) ?_
  intro ⟨_, h⟩
  simp only [comp_obj, ι_obj]
  exact h

instance [F.Additive] : Functor.Additive (t₁.ιHeart ⋙ F) where
  map_add := by
    intro X Y f g
    simp only [comp_obj, comp_map, map_add]

end Functor

namespace AcyclicCategory

/--
Any object isomorphic to an acyclic object is acyclic.
-/
instance : (Acyclic F t₁ t₂).IsClosedUnderIsomorphisms where
  of_iso e := t₂.heart.prop_of_iso ((t₁.ιHeart ⋙ F).mapIso e)

variable (X Y : t₁.Heart)

/--
Any zero object is acyclic.
-/
lemma zero [F.Additive] {X : t₁.Heart} (hX : IsZero X) : Acyclic F t₁ t₂ X := by
  dsimp [Acyclic]
  exact IsClosedUnderIsomorphisms.of_iso (((t₁.ιHeart ⋙ F).mapIso hX.isoZero).trans
    (t₁.ιHeart ⋙ F).mapZeroObject).symm t₂.zero_mem_heart

instance : PreservesBinaryBiproducts t₁.ιHeart :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/--
The product of two acyclic objects is acyclic.
-/
lemma prod [F.Additive] {X Y : t₁.Heart} (hX : Acyclic F t₁ t₂ X) (hY : Acyclic F t₁ t₂ Y) :
    Acyclic F t₁ t₂ (X ⨯ Y) := by
  dsimp [Acyclic]
  have : PreservesLimit (pair X Y) t₁.ιHeart :=
    preservesBinaryProduct_of_preservesBinaryBiproduct _
  have := PreservesLimitPair.iso t₁.ιHeart X Y
  exact IsClosedUnderIsomorphisms.of_iso (PreservesLimitPair.iso (t₁.ιHeart ⋙ F) X Y).symm
      (prod_mem_heart t₂ _ _ hX hY)

instance [F.Additive] : HasTerminal (Acyclic F t₁ t₂).FullSubcategory := by
  let Z : (Acyclic F t₁ t₂).FullSubcategory := ⟨0, zero F t₁ t₂ (isZero_zero t₁.Heart)⟩
  have : ∀ X, Inhabited (X ⟶ Z) := fun X => ⟨0⟩
  have : ∀ X, Unique (X ⟶ Z) := fun X =>
    { uniq := fun f => (ObjectProperty.ι (Acyclic F t₁ t₂)).map_injective
          ((isZero_zero t₁.Heart).eq_of_tgt _ _) }
  exact hasTerminal_of_unique Z

instance [F.Additive] : HasBinaryProducts (Acyclic F t₁ t₂).FullSubcategory := by
  apply hasLimitsOfShape_of_closedUnderLimits
  intro P c hc H
  exact prop_of_iso (Acyclic F t₁ t₂)
    (limit.isoLimitCone ⟨_, (IsLimit.postcomposeHomEquiv (diagramIsoPair P) _).symm hc⟩)
    (prod F t₁ t₂ (H _) (H _))

instance [F.Additive] : HasFiniteProducts (Acyclic F t₁ t₂).FullSubcategory :=
  hasFiniteProducts_of_has_binary_and_terminal

instance [F.Additive] : HasFiniteBiproducts (Acyclic F t₁ t₂).FullSubcategory :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance [F.Additive] : HasBinaryBiproducts (Acyclic F t₁ t₂).FullSubcategory :=
  hasBinaryBiproducts_of_finite_biproducts _

end AcyclicCategory

instance [F.Additive] : Functor.Additive (F.fromAcyclic t₁ t₂) where
  map_add := by
    dsimp [fromAcyclic]
    intro X Y f g
    simp only [lift_map, Functor.comp_map, ι_obj, ι_map, Functor.map_add]

instance : Functor.Additive (Acyclic F t₁ t₂).ι where
  map_add := by
    intro X Y f g
    simp

section Triangulated

variable [IsTriangulated C] [F.CommShift ℤ] [F.IsTriangulated]

/--
An extension (in `t₁.heart`) of acyclic objects is acyclic.
-/
lemma extension_acyclic_of_acyclic {S : ShortComplex t₁.Heart} (SE : S.ShortExact)
    (hS₁ : Acyclic F t₁ t₂ S.X₁) (hS₃ : Acyclic F t₁ t₂ S.X₃) :
    Acyclic F t₁ t₂ S.X₂ := by
  set DT' := F.map_distinguished _ (heartShortExactTriangle_distinguished t₁ S SE)
  dsimp [Acyclic] at hS₁ hS₃ ⊢
  rw [t₂.mem_heart_iff] at hS₁ hS₃ ⊢
  exact ⟨t₂.isLE₂ _ DT' 0 hS₁.1 hS₃.1, t₂.isGE₂ _ DT' 0 hS₁.2 hS₃.2⟩

/--
A short exact complex in `t₁.heart` can be seen as an exact triangle in `C`, hence its
image by `F` is an exact triangle in `D`.
-/
noncomputable abbrev shortExactComplex_to_triangle {S : ShortComplex t₁.Heart}
    (he : S.ShortExact) : Pretriangulated.Triangle D :=
  F.mapTriangle.obj (heartShortExactTriangle t₁ _ he)

lemma shortExactComplex_to_triangle_distinguished {S : ShortComplex t₁.Heart}
    (he : S.ShortExact) : shortExactComplex_to_triangle F t₁ he ∈ distinguishedTriangles :=
  F.map_distinguished _ (heartShortExactTriangle_distinguished t₁ _ he)

end Triangulated

section Triangulated

variable [CategoryTheory.IsTriangulated D]

noncomputable local instance : t₂.HasHomology₀ := t₂.hasHomology₀

noncomputable local instance : t₂.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

namespace Functor

/--
The functor `t₁.heatr.ι ⋙ F ⋙ t₂.homology 0` from the heart of `t₁` to the heat of `t₂`.
-/
noncomputable abbrev fromHeartToHeart : t₁.Heart ⥤ t₂.Heart :=
  t₁.ιHeart ⋙ F ⋙ t₂.homology 0

end Functor

/--
If `X : t₁.heart` is acyclic, then the homology of `F.obj X` in nonzero degrees is zero.
-/
lemma isZero_homology_of_acyclic {X : t₁.Heart} (hX : Acyclic F t₁ t₂ X) (n : ℤ)
    (hn : n ≠ 0) : IsZero ((t₂.homology n).obj (F.obj X.1)) := by
  simp only [Acyclic, mem_heart_iff] at hX
  by_cases h : n ≥ 0
  · have := hX.1
    exact t₂.isZero_homology_of_isLE (F.obj X.1) n 0 (lt_iff_le_and_ne.mpr ⟨h, Ne.symm hn⟩)
  · have := hX.2
    exact t₂.isZero_homology_of_isGE (F.obj X.1) n 0 (lt_iff_not_ge.mpr h)

variable [IsTriangulated C] [F.CommShift ℤ] [F.IsTriangulated ]

/--
If `S` is a short exact triangle in `t₁.heart`, then its image by `F.fromHeartToHeart`
is isomorphic to the `0`th homology functor of `t₂` applied to the exact triangle
obtained by applying `shortExactComplex_to_triangle` to `S`.
-/
noncomputable abbrev map_shortExactComplex_iso_homology_triangle
    {S : ShortComplex t₁.Heart} (he : S.ShortExact) :
    (F.fromHeartToHeart t₁ t₂).mapShortComplex.obj S ≅
    ShortComplex.mk ((t₂.homology 0).map (shortExactComplex_to_triangle F t₁ he).mor₁)
    ((t₂.homology 0).map (shortExactComplex_to_triangle F t₁ he).mor₂)
    (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
    (shortExactComplex_to_triangle_distinguished F t₁ he), Functor.map_zero]) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/--
The functor `F ⋙ t₂.homology 0` sends a short exact complex of acyclic objects to an exact complex.
-/
lemma map_shortExact_exact {S : ShortComplex t₁.Heart} (he : S.ShortExact) :
    ((F.fromHeartToHeart t₁ t₂).mapShortComplex.obj S).Exact :=
  ShortComplex.exact_of_iso (map_shortExactComplex_iso_homology_triangle F t₁ t₂ he).symm
  (t₂.homology_exact₂ _ (shortExactComplex_to_triangle_distinguished F t₁ he) 0)

/--
The image by `F` of a mono with an acyclic cokernel is a mono.
-/
lemma mono_map_of_mono_and_acyclicCokernel {X Y : t₁.Heart} (f : X ⟶ Y) [Mono f]
    (hv : IsZero ((t₂.homology (-1 : ℤ)).obj (F.obj (cokernel f).1))) :
    Mono ((F.fromHeartToHeart t₁ t₂).map f) :=
  (ShortComplex.exact_iff_mono _ (IsZero.eq_zero_of_src hv _)).mp (t₂.homology_exact₁ _
  (shortExactComplex_to_triangle_distinguished F t₁ (monoCokernelComplexShortExact f))
  (-1 : ℤ) 0 (by simp))

/--
The image by `F` of an epi with an acyclic kernel is an epi.
-/
lemma epi_map_of_epi_and_acyclicKernel {X Y : t₁.Heart} (f : X ⟶ Y) [Epi f]
    (hv : IsZero ((t₂.homology (1 : ℤ)).obj (F.obj (kernel f).1))) :
    Epi ((F.fromHeartToHeart t₁ t₂).map f) :=
  (ShortComplex.exact_iff_epi _ (IsZero.eq_zero_of_tgt hv _)).mp (t₂.homology_exact₃ _
  (shortExactComplex_to_triangle_distinguished F t₁ (epiKernelComplexShortExact f))
  (0 : ℤ) 1 (by simp))

/--
The functor `F ⋙ t₂.homology 0` sends a short exact complex `S` to a short exact
complex if `F.obj S.X₁` has no homology in degree `1` and `F.obj S.X₃` has no homology
in degree `-1`.
-/
lemma map_shortExact_of_shortExact_and_homology {S : ShortComplex t₁.Heart} (he : S.ShortExact)
    (hv₁ : IsZero ((t₂.homology (1 : ℤ)).obj (F.obj S.X₁.1)))
    (hv₂ : IsZero ((t₂.homology (-1 : ℤ)).obj (F.obj S.X₃.1))) :
    ((F.fromHeartToHeart t₁ t₂).mapShortComplex.obj S).ShortExact where
  exact := map_shortExact_exact F t₁ t₂ he
  mono_f :=
    have := he.mono_f
    mono_map_of_mono_and_acyclicCokernel F t₁ t₂ S.f (IsZero.of_iso hv₂
    ((t₂.homology (-1 : ℤ)).mapIso (F.mapIso ((ObjectProperty.ι _).mapIso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) he.gIsCokernel)))))
  epi_g :=
    have := he.epi_g
    epi_map_of_epi_and_acyclicKernel F t₁ t₂ S.g (IsZero.of_iso hv₁ ((t₂.homology (1 : ℤ)).mapIso
    (F.mapIso ((ObjectProperty.ι _).mapIso (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g)
    he.fIsKernel)))))

/--
The functor `F ⋙ t₂.homology 0` sends a short exact complex of acyclic objects to a short exact
complex.
-/
lemma map_shortExact_of_shortExact_and_acyclic {S : ShortComplex t₁.Heart} (he : S.ShortExact)
    (hv₁ : Acyclic F t₁ t₂ S.X₁) (hv₂ : Acyclic F t₁ t₂ S.X₃) :
    ((F.fromHeartToHeart t₁ t₂).mapShortComplex.obj S).ShortExact :=
  map_shortExact_of_shortExact_and_homology F t₁ t₂ he
  (isZero_homology_of_acyclic F t₁ t₂ hv₁ (1 : ℤ) (by simp))
  (isZero_homology_of_acyclic F t₁ t₂ hv₂ (-1 : ℤ) (by simp))

/--
If a map `f` has an acyclic kernel and an acyclic cokernel, then its image by `F` has an image
factorization, whose image is `F.obj (Abelian.image f)`.
-/
@[simps!]
noncomputable def imageFactorisation_map_of_acyclic_ker_coker {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : Acyclic F t₁ t₂ (cokernel f)) (h₂ : Acyclic F t₁ t₂ (kernel f)) :
    ImageFactorisation ((F.fromHeartToHeart t₁ t₂).map f) := by
  refine imageFactorisationOfNormalEpi (C := t₂.Heart) _ ?_ ?_
  · refine {I := (F.fromHeartToHeart t₁ t₂).obj (Abelian.image f),
            e := (F.fromHeartToHeart t₁ t₂).map (Abelian.factorThruImage _),
            m := (F.fromHeartToHeart t₁ t₂).map (Abelian.image.ι _),
            m_mono := ?_, fac := ?_}
    · refine mono_map_of_mono_and_acyclicCokernel F t₁ t₂ (Abelian.image.ι f)
        (@isZero_homology_of_isGE _ _ _ _ _ _ _ t₂ _ _ _ _ (-1 : ℤ) 0 (by simp only [Int.reduceNeg,
          Left.neg_neg_iff, zero_lt_one]) ?_)
      have := Limits.IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f)
       (Limits.isCokernelEpiComp (cokernelIsCokernel (Abelian.image.ι f))
        (Abelian.factorThruImage f) (Abelian.image.fac f).symm)
      have := IsClosedUnderIsomorphisms.of_iso this h₁
      simp only [Acyclic, mem_heart_iff] at this
      exact this.2
    · rw [← map_comp, Abelian.image.fac]
  · refine @normalEpiOfEpi (C := t₂.Heart) _ _ _ _ _ _  ?_
    refine epi_map_of_epi_and_acyclicKernel F t₁ t₂ (Abelian.factorThruImage f)
      (@isZero_homology_of_isLE _ _ _ _ _ _ _ t₂ _ _ _ _ _ (1 : ℤ) 0 zero_lt_one ?_)
    have := Limits.IsLimit.conePointUniqueUpToIso (kernelIsKernel f) (Limits.isKernelCompMono
      (kernelIsKernel (Abelian.factorThruImage f)) (Abelian.image.ι f) (Abelian.image.fac f).symm)
    have := IsClosedUnderIsomorphisms.of_iso this h₂
    simp only [Acyclic, mem_heart_iff] at this
    exact this.1

/--
If a map `f` in `t₁.heart` has an acyclic kernel and an acyclic cokernel, then
`t₁.heart.ι ⋙ F ⋙ t₂.homology 0` preserves the image of `f`.
-/
noncomputable def isoImageOfAcyclic {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : Acyclic F t₁ t₂ (cokernel f)) (h₂ : Acyclic F t₁ t₂ (kernel f)) :
    (F.fromHeartToHeart t₁ t₂).obj (Abelian.image f) ≅
    Abelian.image ((F.fromHeartToHeart t₁ t₂).map f) :=
  (IsImage.isoExt (imageFactorisation_map_of_acyclic_ker_coker F t₁ t₂ f h₁ h₂).isImage
  (Limits.Image.isImage ((F.fromHeartToHeart t₁ t₂).map f))).trans (Abelian.imageIsoImage _).symm

@[simp]
lemma isoImageOfAcyclic_comp_ι {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : Acyclic F t₁ t₂ (cokernel f)) (h₂ : Acyclic F t₁ t₂ (kernel f)) :
    (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom ≫ Abelian.image.ι ((F.fromHeartToHeart t₁ t₂).map f) =
    (F.fromHeartToHeart t₁ t₂).map (Abelian.image.ι f) := by
  simp only [isoImageOfAcyclic]
  rw [Iso.trans_hom, Iso.symm_hom, assoc, image_compat]
  erw [IsImage.isoExt_hom_m]
  rfl

lemma factorThruImage_comp_isoImageOfAcyclic {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : Acyclic F t₁ t₂ (cokernel f)) (h₂ : Acyclic F t₁ t₂ (kernel f)) :
    (F.fromHeartToHeart t₁ t₂).map (Abelian.factorThruImage f) ≫
    (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom
    = Abelian.factorThruImage ((F.fromHeartToHeart t₁ t₂).map f) := by
  rw [← cancel_mono (Abelian.image.ι ((F.fromHeartToHeart t₁ t₂).map f)), assoc,
  isoImageOfAcyclic_comp_ι, ← map_comp, Abelian.image.fac, Abelian.image.fac]

/--
If `f` is a morphism in `t₁.heart` with an acyclic image, then its kernel comparison morphism
for the functor `F.fromHeartToHeart` is a mono.
-/
lemma mono_kernelComparison_of_acyclic_image {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₃ : Acyclic F t₁ t₂ (Abelian.image f)) :
    Mono (kernelComparison f (F.fromHeartToHeart t₁ t₂)) := by
  refine @mono_of_mono_fac _ _ _ _ _ _ (kernel.ι _) ((F.fromHeartToHeart t₁ t₂).map (kernel.ι f))
    ?_ (by rw [kernelComparison_comp_ι])
  refine mono_map_of_mono_and_acyclicCokernel F t₁ t₂ (kernel.ι f) (@isZero_homology_of_isGE
    _ _ _ _ _ _ _ t₂ _ _ _ _ (-1 : ℤ) 0 (by simp only [Int.reduceNeg, Left.neg_neg_iff,
    zero_lt_one]) ?_)
  have := IsClosedUnderIsomorphisms.of_iso (Abelian.coimageIsoImage _).symm h₃
  simp only [Acyclic, mem_heart_iff] at this
  exact this.2

/--
If `f` is a morphism in `t₁.heart` with an acyclic image, an acyclic kernel and an acyclic cokernel,
then its kernel comparison morphism for the functor `F.fromHeartToHeart` is an epi.
-/
lemma epi_kernelComparison_of_acyclic_homology {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : Acyclic F t₁ t₂ (cokernel f)) (h₂ : Acyclic F t₁ t₂ (kernel f))
    (h₃ : Acyclic F t₁ t₂ (Abelian.image f)) :
    Epi (kernelComparison f (F.fromHeartToHeart t₁ t₂)) := by
  set R₁ := ((F.fromHeartToHeart t₁ t₂).mapShortComplex.obj (ShortComplex.mk (kernel.ι f)
    (Abelian.factorThruImage f)
    (by rw [← cancel_mono (Abelian.image.ι f), assoc, Abelian.image.fac, zero_comp,
      kernel.condition f]))).toComposableArrows
  set R₂ := (ShortComplex.mk (kernel.ι ((F.fromHeartToHeart t₁ t₂).map f))
    (Abelian.factorThruImage ((F.fromHeartToHeart t₁ t₂).map f))
    (by rw [← cancel_mono (Abelian.image.ι _), zero_comp, assoc, Abelian.image.fac,
    kernel.condition])).toComposableArrows
  have hR₁ : R₁.Exact := (map_shortExact_of_shortExact_and_acyclic F t₁ t₂
    (kernelImageComplexShortExact f) h₂ h₃).exact.exact_toComposableArrows
  have hR₂ : R₂.Exact := (kernelImageComplexShortExact _).exact.exact_toComposableArrows
  set φ : R₁ ⟶ R₂ := by
    refine ComposableArrows.homMk ?_ ?_
    · intro i
      match i with
      | 0 => exact kernelComparison f (F.fromHeartToHeart t₁ t₂)
      | 1 => exact 𝟙 _
      | 2 => exact (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom
    · intro i _
      match i with
      | 0 => erw [kernelComparison_comp_ι, comp_id]; rfl
      | 1 => erw [factorThruImage_comp_isoImageOfAcyclic, id_comp]; rfl
  refine Abelian.epi_of_mono_of_epi_of_mono φ hR₁ hR₂ ?_ ?_ ?_
  · change Mono (kernel.ι _); exact inferInstance
  · change Epi (𝟙 _); exact inferInstance
  · change Mono (isoImageOfAcyclic F t₁ t₂ f h₁ h₂).hom; exact inferInstance

/--
If `f` is a morphism in `t₁.heart` with an acyclic image, an acyclic kernel and an acyclic cokernel,
then its kernel comparison morphism for the functor `F.fromHeartToHeart` is an iso.
-/
noncomputable def isIso_kernelComparison_of_acyclic_homology {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : Acyclic F t₁ t₂ (cokernel f)) (h₂ : Acyclic F t₁ t₂ (kernel f))
    (h₃ : Acyclic F t₁ t₂ (Abelian.image f)) :
    IsIso (kernelComparison f (F.fromHeartToHeart t₁ t₂)) :=
  @isIso_of_mono_of_epi _ _ _ _ _ _ (mono_kernelComparison_of_acyclic_image F t₁ t₂ f h₃)
  (epi_kernelComparison_of_acyclic_homology F t₁ t₂ f h₁ h₂ h₃)

/--
If `f` is a morphism in `t₁.heart` with an acyclic image, then its cokernel comparison morphism
for the functor `F.fromHeartToHeart` is an epi.
-/
lemma epi_cokernelComparison_of_acyclic_image {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₃ : Acyclic F t₁ t₂ (Abelian.image f)) :
    Epi (cokernelComparison f (F.fromHeartToHeart t₁ t₂)) := by
  simp only [Acyclic, mem_heart_iff] at h₃
  exact @epi_of_epi_fac _ _ _ _ _ (cokernel.π _) _ ((F.fromHeartToHeart t₁ t₂).map (cokernel.π f))
    (epi_map_of_epi_and_acyclicKernel F t₁ t₂ (cokernel.π f) (@isZero_homology_of_isLE
    _ _ _ _ _ _ _ t₂ _ _ _ _ _ (1 : ℤ) 0 zero_lt_one h₃.1)) (by rw [π_comp_cokernelComparison])

/--
If `f` is a morphism in `t₁.heart` with an acyclic image, an acyclic kernel and an acyclic cokernel,
then its cokernel comparison morphism for the functor `F.fromHeartToHeart` is a mono.
-/
lemma mono_cokernelComparison_of_acyclic_homology {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : Acyclic F t₁ t₂ (cokernel f)) (h₂ : Acyclic F t₁ t₂ (kernel f))
    (h₃ : Acyclic F t₁ t₂ (Abelian.image f)) :
    Mono (cokernelComparison f (F.fromHeartToHeart t₁ t₂)) := by
  set R₂ := ((F.fromHeartToHeart t₁ t₂).mapShortComplex.obj (ShortComplex.mk (Abelian.image.ι f)
    (Limits.cokernel.π f)
    (by simp only [equalizer_as_kernel, kernel.condition]))).toComposableArrows
  set R₁ := (ShortComplex.mk (Abelian.image.ι ((F.fromHeartToHeart t₁ t₂).map f))
    (cokernel.π ((F.fromHeartToHeart t₁ t₂).map f))
    (by simp only [comp_obj, Functor.comp_map, equalizer_as_kernel,
    kernel.condition])).toComposableArrows
  have hR₂ : R₂.Exact := (map_shortExact_of_shortExact_and_acyclic F t₁ t₂
    (epiKernelComplexShortExact (cokernel.π f)) h₃ h₁).exact.exact_toComposableArrows
  have hR₁ : R₁.Exact := (ShortComplex.exact_of_f_is_kernel _
    (kernelIsKernel _)).exact_toComposableArrows
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

/--
If `f` is a morphism in `t₁.heart` with an acyclic image, an acyclic kernel and an acyclic cokernel,
then its cokernel comparison morphism for the functor `F.fromHeartToHeart` is an iso.
-/
noncomputable def isIso_cokernelComparison_of_acyclic_homology {X Y : t₁.Heart} (f : X ⟶ Y)
    (h₁ : Acyclic F t₁ t₂ (cokernel f)) (h₂ : Acyclic F t₁ t₂ (kernel f))
    (h₃ : Acyclic F t₁ t₂ (Abelian.image f)) :
    IsIso (cokernelComparison f (F.fromHeartToHeart t₁ t₂)) :=
  @isIso_of_mono_of_epi _ _ _ _ _ _ (mono_cokernelComparison_of_acyclic_homology F t₁ t₂ f h₁ h₂ h₃)
  (epi_cokernelComparison_of_acyclic_image F t₁ t₂ f h₃)

/--
Let `S` be a short exact sequence in `t₁.heart` such that `S.X₂` is acyclic. Then the connecting
morphism in the long exact sequence of homology of the exact triangle in `D` "image of `S` by `F`"
(i.e. given by `shortExactComplex_to_triangle`) is an isomorphism from `n`th homology of
`F.obj S.X₃` to the `(n + 1)`st homology of `F.obj S.X₁`.
-/
noncomputable def shortExact_connecting_iso {S : ShortComplex t₁.Heart} (hS : S.ShortExact)
    (hS₁ : Acyclic F t₁ t₂ S.X₂) {n : ℤ} (hn : n ≠ -1 ∧ n ≠ 0) :
    (t₂.homology n).obj (F.obj S.X₃.1) ≅ (t₂.homology (n + 1)).obj (F.obj S.X₁.1) := by
  set T := shortExactComplex_to_triangle F t₁ hS
  have hT : T ∈ distinguishedTriangles := shortExactComplex_to_triangle_distinguished F t₁ hS
  set f := t₂.homologyδ (shortExactComplex_to_triangle F t₁ hS) n (n + 1) rfl
  have h₁ : Mono f := by
    refine (ShortComplex.exact_iff_mono _ (Limits.zero_of_source_iso_zero _ ?_)).mp
      (t₂.homology_exact₃ _ hT n (n + 1) rfl)
    change (t₂.homology n).obj (F.obj S.X₂.1) ≅ 0
    refine Limits.IsZero.isoZero ?_
    by_cases hn' : 0 ≤ n
    · letI : t₂.IsLE (F.obj S.X₂.1) 0 := {le := hS₁.1}
      exact t₂.isZero_homology_of_isLE _ n 0 (lt_iff_le_and_ne.mpr ⟨hn', Ne.symm hn.2⟩)
    · letI : t₂.IsGE (F.obj S.X₂.1) 0 := {ge := hS₁.2}
      exact t₂.isZero_homology_of_isGE _ n 0 (lt_iff_not_ge.mpr hn')
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
      rw [lt_iff_le_and_ne, Int.add_one_le_iff, and_iff_right (lt_iff_not_ge.mpr hn'), ne_eq,
          ← eq_neg_iff_add_eq_zero]
      exact hn.1
  exact @asIso _ _ _ _ f ((isIso_iff_mono_and_epi f).mpr ⟨h₁, h₂⟩)

/--
Let `S` ba a cochain complex in `t₁.heart`. Suppose that `S` is exact in degree `r + 1`, and that
the `r`th entry of `S` is acyclic. Then, for every `n` different from `0` and `-1`, we have
an isomorphism betweem the `n`th cohomology of `F.obj (kernel (S.d (r + 1) (r + 2)))` and the
`(n + 1)`st homology of `F.obj (kernel (S.d r (r + 1)))`.
-/
noncomputable def iso_cohomology_of_acyclic_and_exact (S : CochainComplex t₁.Heart ℤ) (r k l m : ℤ)
    (hrk : r + 1 = k) (hkl : k = l) (hlm : l + 1 = m) (h₁ : Acyclic F t₁ t₂ (S.X r))
    (h₂ : S.ExactAt l) {n : ℤ} (hn : n ≠ -1 ∧ n ≠ 0) :
    (t₂.homology n).obj (F.obj (Limits.kernel (S.d l m)).1) ≅ (t₂.homology (n + 1)).obj
    (F.obj (Limits.kernel (S.d r k)).1) :=
  (((t₂.homology n).mapIso (F.mapIso ((ObjectProperty.ι _).mapIso
  ((S.sc' r l m).isoAbelianImageToKernelOfExact ((S.exactAt_iff' r l m
  (by simp only [CochainComplex.prev]; linarith [hrk, hkl])
  (by simp only [CochainComplex.next, hlm])).mp h₂))))).symm.trans
  (shortExact_connecting_iso F t₁ t₂ (kernelImageComplexShortExact (S.d r l)) h₁ hn)).trans
  ((t₂.homology (n + 1)).mapIso (F.mapIso ((ObjectProperty.ι _).mapIso
  (kernel.mapIso (S.d r l) (S.d r k) (Iso.refl _) (S.XIsoOfEq hkl.symm)
  (by simp only [HomologicalComplex.d_comp_XIsoOfEq_hom, Iso.refl_hom, id_comp])))))

noncomputable def rightAcyclic_ker_aux (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ} (hkl : k + 1 = l)
    (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), i ≤ k → Acyclic F t₁ t₂ (S.X i)) (n : ℕ) :
    (t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1) ≅ (t₂.homology (r + n)).obj
    (F.obj (Limits.kernel (S.d (k - n) (l - n))).1) := by
  induction' n with n hn
  · simp only [CharP.cast_eq_zero, add_zero, Int.cast_ofNat_Int]
    erw [sub_zero, sub_zero]
  · have : r + ↑(n + 1) = (r + n) + 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [this]
    have : k - ↑(n + 1) = (k - n) - 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [this]
    have : l - ↑(n + 1) = (l - n) - 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    rw [this]
    refine hn.trans (iso_cohomology_of_acyclic_and_exact F t₁ t₂ S (k - n - 1) (l - n - 1) (k - n)
      (l - n) (by linarith) (by linarith [hkl]) (by linarith) (hk2 (k - n - 1) (by linarith))
      (hk1 (k - n) (by linarith)) (n := r + n) ⟨by linarith [hr], by linarith [hr]⟩)

/--
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact in degree `≤ k`,
and that the entries of `S` are acyclic in degree `≤ k` and zero in small enough degree.
Then the homology of `F.obj (kernel (S.d k (k + 1)))` is zero in positive degree.
-/
lemma rightAcyclic_ker_of_bounded_complex (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), i ≤ k → Acyclic F t₁ t₂ (S.X i)) {a : ℤ}
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j)) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1)) := by
  refine IsZero.of_iso ?_ (rightAcyclic_ker_aux F t₁ t₂ S hkl hr hk1 hk2 (k - a).natAbs)
  suffices h : IsZero (kernel (S.d (k - ↑(k - a).natAbs) (l - ↑(k - a).natAbs))) by
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    change IsZero ((ObjectProperty.ι _).obj _)
    refine Functor.map_isZero _ h
  refine IsZero.of_mono (kernel.ι (S.d (k - (k - a).natAbs) (l - (k - a).natAbs))) (ha _ ?_)
  rw [tsub_le_iff_right, ← tsub_le_iff_left]; exact Int.le_natAbs

/--
Suppose that `F` has finite cohomological degree (relative to `t₁` and `t₂`).
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact in degree `≤ k`
and that the entries of `S` in degree `≤ k` are acyclic.
Then the homology of `F.obj (kernel (S.d k (k + 1)))` is zero in positive degree.
-/
lemma rightAcyclic_ker_of_bounded_functor (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r > 0) (hk1 : ∀ (i : ℤ), i ≤ k → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), i ≤ k → Acyclic F t₁ t₂ (S.X i)) {d : ℤ}
    (hd : ∀ (X : t₁.Heart) (j : ℤ), d ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1)) := by
  refine IsZero.of_iso (hd _ _ ?_) (rightAcyclic_ker_aux F t₁ t₂ S hkl hr hk1 hk2 (d - r).natAbs)
  rw [← tsub_le_iff_left]; exact Int.le_natAbs

noncomputable def leftAcyclic_ker_aux (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), k ≤ i → Acyclic F t₁ t₂ (S.X i)) (n : ℕ) :
    (t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1) ≅ (t₂.homology (r - n)).obj
    (F.obj (Limits.kernel (S.d (k + n) (l + n))).1) := by
  induction' n with n hn
  · simp only [CharP.cast_eq_zero, sub_zero, Int.cast_ofNat_Int]
    erw [add_zero, add_zero]
  · refine hn.trans ?_
    have : r - n = r - (n + 1) + 1 := by ring
    erw [this]
    exact (iso_cohomology_of_acyclic_and_exact F t₁ t₂ S (k + n) (l + n) (k + (n + 1))
      (l + (n + 1)) (by linarith) (by linarith) (by linarith)
      (hk2 (k + n) (by linarith)) (hk1 (k + (n + 1)) (by linarith)) (n := r - (n + 1))
      ⟨by linarith [hr], by linarith [hr]⟩).symm

/--
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact in degree `> k`,
and that the entries of `S` are acyclic in degree `≤ k` and zero in large enough degree.
Then the homology of `F.obj (kernel (S.d k (k + 1)))` is zero in negative degree.
-/
lemma leftAcyclic_ker_of_boundedComplex (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), k ≤ i → Acyclic F t₁ t₂ (S.X i)) {b : ℤ}
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1)) := by
  refine IsZero.of_iso ?_ (leftAcyclic_ker_aux F t₁ t₂ S hkl hr hk1 hk2 (b - k).natAbs)
  suffices h : IsZero (kernel (S.d (k + ↑(b - k).natAbs) (l + ↑(b - k).natAbs))) by
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    change IsZero ((ObjectProperty.ι _).obj _)
    refine Functor.map_isZero _ h
  refine IsZero.of_mono (kernel.ι (S.d (k + (b - k).natAbs) (l + (b - k).natAbs))) (hb _ ?_)
  rw [← tsub_le_iff_left]; exact Int.le_natAbs

/--
Suppose that `F` has finite cohomological degree (relative to `t₁` and `t₂`).
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact in degree `> k`
and that the entries of `S` in degree `≥ k` are acyclic.
Then the homology of `F.obj (kernel (S.d k (k + 1)))` is zero in negative degree.
-/
lemma leftAcyclic_ker_of_bounded_functor (S : CochainComplex t₁.Heart ℤ) {r k l : ℤ}
    (hkl : k + 1 = l) (hr : r < 0) (hk1 : ∀ (i : ℤ), k < i → S.ExactAt i)
    (hk2 : ∀ (i : ℤ), k ≤ i → Acyclic F t₁ t₂ (S.X i)) {c : ℤ}
    (hc : ∀ (X : t₁.Heart) (j : ℤ), j ≤ c → IsZero ((t₂.homology j).obj (F.obj X.1))) :
    IsZero ((t₂.homology r).obj (F.obj (Limits.kernel (S.d k l)).1)) := by
  refine IsZero.of_iso (hc _ _ ?_) (leftAcyclic_ker_aux F t₁ t₂ S hkl hr hk1 hk2 (r - c).natAbs)
  rw [tsub_le_iff_left, ← tsub_le_iff_right]; exact Int.le_natAbs

variable [NonDegenerate t₂]

/--
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact, and that the entries
of `S` are acyclic in every degree and zero outside of a bounded interval.
Then `kernel (S.d k (k + 1))` is acyclic for every `k`.
-/
lemma acyclic_ker_of_bounded_exact_acyclic_complex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k l : ℤ) (hkl : k + 1 = l) :
    Acyclic F t₁ t₂ (Limits.kernel (S.d k l)) := by
  simp only [Acyclic]
  refine isHeart_of_isZero_homology t₂ _ ?_
  intro j hj
  rw [ne_iff_lt_or_gt] at hj
  cases hj with
  | inl h => exact leftAcyclic_ker_of_boundedComplex F t₁ t₂ S hkl h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) hb
  | inr h => exact rightAcyclic_ker_of_bounded_complex F t₁ t₂ S hkl h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) ha

/--
Suppose that `F` has finite cohomological degree (relative to `t₁` and `t₂`).
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact and that the entries
of `S` are acyclic.
Then `kernel (S.d k (k + 1))` is acyclic for every `k`.
-/
lemma acyclic_ker_of_exact_acyclic_complex_and_bounded_functor (S : CochainComplex t₁.Heart ℤ)
    {a b: ℤ} (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (k l : ℤ) (hkl : k + 1 = l) :
    Acyclic F t₁ t₂ (Limits.kernel (S.d k l)) := by
  simp only [Acyclic]
  refine isHeart_of_isZero_homology t₂ _ ?_
  intro j hj
  rw [ne_iff_lt_or_gt] at hj
  cases hj with
  | inl h => exact leftAcyclic_ker_of_bounded_functor F t₁ t₂ S hkl h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) ha
  | inr h => exact rightAcyclic_ker_of_bounded_functor F t₁ t₂ S hkl h (fun _ _ ↦ hexact _)
               (fun _ _ ↦ hacy _) hb

/--
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact, and that the entries
of `S` are acyclic in every degree and zero outside of a bounded interval.
Then `Abelian.image (S.d k (k + 1))` is acyclic for every `k`.
-/
lemma acyclic_image_of_bounded_exact_acyclic_complex (S : CochainComplex t₁.Heart ℤ) {a b: ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k l : ℤ) (hkl : k + 1 = l) :
    Acyclic F t₁ t₂ (Abelian.image (S.d k l)) := by
  refine IsClosedUnderIsomorphisms.of_iso ?_ (acyclic_ker_of_bounded_exact_acyclic_complex F t₁ t₂
    S hexact hacy ha hb (k + 1) (l + 1) (by linarith))
  set e : S.sc l ≅ S.sc' k l (l + 1) :=
    S.isoSc' k l (l + 1) (by simp only [hkl.symm, CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next])
  have := ShortComplex.imageToKernelIsIsoOfExact (IsZero.of_iso
    ((S.exactAt_iff_isZero_homology _).mp (hexact l)) (ShortComplex.homologyMapIso e).symm)
  exact ((asIso (S.sc' k l (l + 1)).abelianImageToKernel).trans (kernel.mapIso (S.d l (l + 1))
    (S.d (k + 1) (l + 1)) (S.XIsoOfEq hkl.symm) (Iso.refl _)
    (by simp only [Iso.refl_hom, comp_id, HomologicalComplex.XIsoOfEq_hom_comp_d]))).symm

/--
Suppose that `F` has finite cohomological degree (relative to `t₁` and `t₂`).
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact and that the entries
of `S` are acyclic.
Then `Abelian.image (S.d k (k + 1))` is acyclic for every `k`.
-/
lemma acyclic_image_of_exact_acyclic_complex_and_bounded_functor (S : CochainComplex t₁.Heart ℤ)
    {a b : ℤ} (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k l : ℤ)
    (hkl : k + 1 = l) :
    Acyclic F t₁ t₂ (Abelian.image (S.d k l)) := by
  refine IsClosedUnderIsomorphisms.of_iso ?_
    (acyclic_ker_of_exact_acyclic_complex_and_bounded_functor F t₁ t₂
    S hexact hacy ha hb (k + 1) (l + 1) (by linarith))
  set e : S.sc l ≅ S.sc' k l (l + 1) :=
    S.isoSc' k l (l + 1) (by simp only [hkl.symm, CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next])
  have := ShortComplex.imageToKernelIsIsoOfExact (IsZero.of_iso
    ((S.exactAt_iff_isZero_homology _).mp (hexact l)) (ShortComplex.homologyMapIso e).symm)
  exact ((asIso (S.sc' k l (l + 1)).abelianImageToKernel).trans (kernel.mapIso (S.d l (l + 1))
    (S.d (k + 1) (l + 1)) (S.XIsoOfEq hkl.symm) (Iso.refl _)
    (by simp only [Iso.refl_hom, comp_id, HomologicalComplex.XIsoOfEq_hom_comp_d]))).symm

/--
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact, and that the entries
of `S` are acyclic in every degree and zero outside of a bounded interval.
Then `Abelian.coimage (S.d k (k + 1))` is acyclic for every `k`.
-/
lemma acyclic_coimage_of_bounded_exact_acyclic_complex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k l : ℤ) (hkl : k + 1 = l) :
    Acyclic F t₁ t₂ (Abelian.coimage (S.d k l)) :=
  IsClosedUnderIsomorphisms.of_iso (asIso (Abelian.coimageImageComparison (S.d k l))).symm
  (acyclic_image_of_bounded_exact_acyclic_complex F t₁ t₂ S hexact hacy ha hb k l hkl)

/--
Suppose that `F` has finite cohomological degree (relative to `t₁` and `t₂`).
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact and that the entries
of `S` are acyclic.
Then `Abelian.coimage (S.d k (k + 1))` is acyclic for every `k`.
-/
lemma acyclic_coimage_of_exact_acyclic_complex_and_bounded_functor (S : CochainComplex t₁.Heart ℤ)
    {a b : ℤ} (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k l : ℤ)
    (hkl : k + 1 = l) :
    Acyclic F t₁ t₂ (Abelian.coimage (S.d k l)) :=
  IsClosedUnderIsomorphisms.of_iso (asIso (Abelian.coimageImageComparison (S.d k l))).symm
  (acyclic_image_of_exact_acyclic_complex_and_bounded_functor F t₁ t₂ S hexact hacy ha hb k l hkl)

/--
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact, and that the entries
of `S` are acyclic in every degree and zero outside of a bounded interval.
Then `cokernel (S.d k (k + 1))` is acyclic for every `k`.
-/
lemma acyclic_coker_of_bounded_exact_acyclic_complex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (k l : ℤ) (hkl : k + 1 = l) :
    Acyclic F t₁ t₂ (Limits.cokernel (S.d k l)) := by
  refine IsClosedUnderIsomorphisms.of_iso ?_ (acyclic_coimage_of_bounded_exact_acyclic_complex
    F t₁ t₂ S hexact hacy ha hb (k + 1) (l + 1) (by linarith))
  set e : S.sc (k + 1) ≅ S.sc' k (k + 1) (l+ 1) :=
    S.isoSc' k (k + 1) (l + 1) (by simp only [CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next, hkl.symm])
  have := ShortComplex.cokernelToAbelianCoimageIsIsoOfExact (IsZero.of_iso
    ((S.exactAt_iff_isZero_homology _).mp (hexact (k + 1))) (ShortComplex.homologyMapIso e).symm)
  exact (asIso (S.sc' k (k + 1) (l + 1)).cokernelToAbelianCoimage).symm.trans
    (cokernel.mapIso (S.d k (k + 1)) (S.d k l) (Iso.refl _) (S.XIsoOfEq hkl)
    (by simp only [HomologicalComplex.d_comp_XIsoOfEq_hom, Iso.refl_hom, id_comp]))

/--
Suppose that `F` has finite cohomological degree (relative to `t₁` and `t₂`).
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact and that the entries
of `S` are acyclic.
Then `cokernel (S.d k (k + 1))` is acyclic for every `k`.
-/
lemma acyclic_coker_of_exact_acyclic_complex_and_bounded_functor (S : CochainComplex t₁.Heart ℤ)
    {a b: ℤ} (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (k l : ℤ)
    (hkl : k + 1 = l) :
    Acyclic F t₁ t₂ (Limits.cokernel (S.d k l)) := by
  refine IsClosedUnderIsomorphisms.of_iso ?_
    (acyclic_coimage_of_exact_acyclic_complex_and_bounded_functor F t₁ t₂
    S hexact hacy ha hb (k + 1) (l + 1) (by linarith))
  set e : S.sc (k + 1) ≅ S.sc' k (k + 1) (l+ 1) :=
    S.isoSc' k (k + 1) (l + 1) (by simp only [CochainComplex.prev, add_sub_cancel_right])
    (by simp only [CochainComplex.next, hkl.symm])
  have := ShortComplex.cokernelToAbelianCoimageIsIsoOfExact (IsZero.of_iso
    ((S.exactAt_iff_isZero_homology _).mp (hexact (k + 1))) (ShortComplex.homologyMapIso e).symm)
  exact (asIso (S.sc' k (k + 1) (l + 1)).cokernelToAbelianCoimage).symm.trans
    (cokernel.mapIso (S.d k (k + 1)) (S.d k l) (Iso.refl _) (S.XIsoOfEq hkl)
    (by simp only [HomologicalComplex.d_comp_XIsoOfEq_hom, Iso.refl_hom, id_comp]))

/--
Let `S` be a short complex in `t₁.heart`.  If `S` is exact, `S.f` has an acyclic kernel,
and `S.g` has an acyclic kernel, an acyclic cokernel and an acyclic image, then
`F.fromToHeartHeart` preserves the left homology data of `S`.
-/
noncomputable def preserves_leftHomologyData_of_acyclic (S : ShortComplex t₁.Heart)
    (he : S.Exact) (h₀ : Acyclic F t₁ t₂ (kernel S.f))
    (h₁ : Acyclic F t₁ t₂ (cokernel S.g)) (h₂ : Acyclic F t₁ t₂ (kernel S.g))
    (h₃ : Acyclic F t₁ t₂ (Abelian.image S.g)) :
    (ShortComplex.LeftHomologyData.ofAbelian S).IsPreservedBy (F.fromHeartToHeart t₁ t₂) where
  g := by
    have := isIso_kernelComparison_of_acyclic_homology F t₁ t₂ S.g h₁ h₂ h₃
    exact PreservesKernel.of_iso_comparison _ _
  f' := by
    have := isIso_cokernelComparison_of_acyclic_homology F t₁ t₂
      (ShortComplex.LeftHomologyData.ofAbelian S).f' ?_ ?_ ?_
    · exact PreservesCokernel.of_iso_comparison _ _
    · exact IsClosedUnderIsomorphisms.of_iso S.homologyIsoCokernelLift (AcyclicCategory.zero F t₁ t₂
        (S.exact_iff_isZero_homology.mp he))
    · exact IsClosedUnderIsomorphisms.of_iso (S.LeftHomologyData_ker_f' _).symm h₀
    · refine IsClosedUnderIsomorphisms.of_iso (S.LeftHomologyData_image_f' _).symm ?_
      rw [S.exact_iff_isIso_abelianImageToKernel] at he
      exact IsClosedUnderIsomorphisms.of_iso (asIso S.abelianImageToKernel).symm h₂

/--
Let `S` be a short complex in `t₁.heart`.  If `S` is exact, `S.f` has an acyclic kernel,
and `S.g` has an acyclic kernel, an acyclic cokernel and an acyclic image, then
`F.fromToHeartHeart` preserves the left homology of `S`.
-/
noncomputable def preservesLeftHomology_of_acyclic (S : ShortComplex t₁.Heart)
    (he : S.Exact) (h₀ : Acyclic F t₁ t₂ (kernel S.f))
    (h₁ : Acyclic F t₁ t₂ (cokernel S.g)) (h₂ : Acyclic F t₁ t₂ (kernel S.g))
    (h₃ : Acyclic F t₁ t₂ (Abelian.image S.g)) :
    PreservesLeftHomologyOf (F.fromHeartToHeart t₁ t₂) S := by
  have := preserves_leftHomologyData_of_acyclic F t₁ t₂ S he h₀ h₁ h₂ h₃
  refine Functor.PreservesLeftHomologyOf.mk' (F.fromHeartToHeart t₁ t₂)
    (ShortComplex.LeftHomologyData.ofAbelian S)

namespace ShortComplex

omit [t₂.NonDegenerate] in
/--
Let `S` be a short complex in `t₁.heart`.  If `S` is exact, `S.f` has an acyclic kernel,
and `S.g` has an acyclic kernel, an acyclic cokernel and an acyclic image, then
the image of `S` by `F.fromToHeartHeart` is exact.
-/
lemma exact_map_of_acyclic (S : ShortComplex t₁.Heart)
    (he : S.Exact) (h₀ : Acyclic F t₁ t₂ (kernel S.f))
    (h₁ : Acyclic F t₁ t₂ (cokernel S.g)) (h₂ : Acyclic F t₁ t₂ (kernel S.g))
    (h₃ : Acyclic F t₁ t₂ (Abelian.image S.g)) :
    (S.map (F.fromHeartToHeart t₁ t₂)).Exact := by
  have := preservesLeftHomology_of_acyclic F t₁ t₂ S he h₀ h₁ h₂ h₃
  exact he.map_of_preservesLeftHomologyOf _

end ShortComplex

namespace CochainComplex

/--
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact and that the entries
of `S` are acyclic and zero outside of a bounded interval.
Then the image of `S` by `F.fromHeartToHeart` is exact.
-/
lemma exact_map_of_exact_bounded_acyclic_complex (S : CochainComplex t₁.Heart ℤ) {a b : ℤ}
    (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (j : ℤ), j ≤ a → IsZero (S.X j))
    (hb : ∀ (j : ℤ), b ≤ j → IsZero (S.X j)) (i : ℤ):
    (((F.fromHeartToHeart t₁ t₂).mapHomologicalComplex ((ComplexShape.up ℤ))).obj S).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  refine (S.sc i).exact_map_of_acyclic F t₁ t₂ ?_ ?_ ?_ ?_ ?_
  · rw [← HomologicalComplex.exactAt_iff]; exact hexact i
  · simp only [HomologicalComplex.shortComplexFunctor_obj_X₁,
    HomologicalComplex.shortComplexFunctor_obj_X₂, HomologicalComplex.shortComplexFunctor_obj_f]
    exact acyclic_ker_of_bounded_exact_acyclic_complex F t₁ t₂ S hexact hacy ha hb _ i
      (by simp only [CochainComplex.prev, sub_add_cancel])
  · exact acyclic_coker_of_bounded_exact_acyclic_complex F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])
  · exact acyclic_ker_of_bounded_exact_acyclic_complex F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])
  · exact acyclic_image_of_bounded_exact_acyclic_complex F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])

/--
Suppose that `F` has finite cohomological degree (relative to `t₁` and `t₂`).
Let `S` be a cochain complex in `t₁.heart`. Suppose that `S` is exact and that the entries
of `S` are acyclic.
Then the image of `S` by `F.fromHeartToHeart` is exact.
-/
lemma exact_map_of_exact_acyclic_complex_and_bounded_functor (S : CochainComplex t₁.Heart ℤ)
    {a b: ℤ} (hexact : ∀ (i : ℤ), S.ExactAt i)
    (hacy : ∀ (i : ℤ), Acyclic F t₁ t₂ (S.X i))
    (ha : ∀ (X : t₁.Heart) (j : ℤ), j ≤ a → IsZero ((t₂.homology j).obj (F.obj X.1)))
    (hb : ∀ (X : t₁.Heart) (j : ℤ), b ≤ j → IsZero ((t₂.homology j).obj (F.obj X.1))) (i : ℤ) :
    (((F.fromHeartToHeart t₁ t₂).mapHomologicalComplex ((ComplexShape.up ℤ))).obj S).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  refine (S.sc i).exact_map_of_acyclic F t₁ t₂ ?_ ?_ ?_ ?_ ?_
  · rw [← HomologicalComplex.exactAt_iff]; exact hexact i
  · simp only [HomologicalComplex.shortComplexFunctor_obj_X₁,
    HomologicalComplex.shortComplexFunctor_obj_X₂, HomologicalComplex.shortComplexFunctor_obj_f]
    exact acyclic_ker_of_exact_acyclic_complex_and_bounded_functor F t₁ t₂ S hexact hacy ha hb _ i
      (by simp only [CochainComplex.prev, sub_add_cancel])
  · exact acyclic_coker_of_exact_acyclic_complex_and_bounded_functor F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])
  · exact acyclic_ker_of_exact_acyclic_complex_and_bounded_functor F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])
  · exact acyclic_image_of_exact_acyclic_complex_and_bounded_functor F t₁ t₂ S hexact hacy ha hb i _
      (by simp only [CochainComplex.next])

end CochainComplex

end Triangulated

end CategoryTheory
