/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive

/-!
# Localization with respect to a Serre class

-/

@[expose] public section

universe v' u' v u

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]

-- to be moved
def NormalMono.ofArrowIso [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y}
    (hf : NormalMono f) {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    NormalMono f' where
  Z := hf.Z
  g := e.inv.right ≫ hf.g
  w := by
    have := Arrow.w e.inv
    dsimp at this
    rw [← reassoc_of% this, hf.w, comp_zero]
  isLimit := by
    refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).1 hf.isLimit
    · exact parallelPair.ext (Arrow.rightFunc.mapIso e) (Iso.refl _)
        (by cat_disch) (by cat_disch)
    · exact Fork.ext (Arrow.leftFunc.mapIso e)

def NormalEpi.ofArrowIso [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y}
    (hf : NormalEpi f) {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    NormalEpi f' where
  W := hf.W
  g := hf.g ≫ e.hom.left
  w := by
    have := Arrow.w e.hom
    dsimp at this
    rw [assoc, this, reassoc_of% hf.w, zero_comp]
  isColimit := by
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1 hf.isColimit
    · exact parallelPair.ext (Iso.refl _) (Arrow.leftFunc.mapIso e)
        (by cat_disch) (by cat_disch)
    · exact Cofork.ext (Arrow.rightFunc.mapIso e) (by simp [Cofork.π])

variable [Abelian C]

namespace ObjectProperty

variable (L : C ⥤ D) (P : ObjectProperty C) [P.IsSerreClass]

lemma exists_isoModSerre_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (X' : C) (s : X' ⟶ X) (_ : P.isoModSerre s), s ≫ f = 0) ↔
        P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨X', s, hs, eq⟩
    have := P.epiModSerre.comp_mem s (Abelian.factorThruImage f) hs.2
      (epiModSerre_of_epi _ _)
    rwa [show s ≫ Abelian.factorThruImage f = 0 by cat_disch,
      epiModSerre_zero_iff] at this
  · refine ⟨_, kernel.ι f, ?_, by simp⟩
    rw [isoModSerre_iff_of_mono]
    exact P.prop_of_iso (Abelian.coimageIsoImage f).symm hf

lemma exists_comp_isoModSerre_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∃ (Y' : C) (s : Y ⟶ Y') (_ : P.isoModSerre s), f ≫ s = 0) ↔
        P (Abelian.image f) := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨Y', s, hs, eq⟩
    apply P.prop_of_iso (Abelian.coimageIsoImage f)
    have := P.monoModSerre.comp_mem (Abelian.factorThruCoimage f) s
      (monoModSerre_of_mono _ _) hs.1
    rwa [show Abelian.factorThruCoimage f ≫ s = 0 by cat_disch,
      monoModSerre_zero_iff] at this
  · exact ⟨_, cokernel.π f, by simpa [isoModSerre_iff_of_epi], by simp⟩

namespace SerreClassLocalization

instance : P.isoModSerre.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ :=
    ⟨{s := pushout.inl φ.f φ.s
      f := pushout.inr φ.f φ.s,
      hs := MorphismProperty.pushout_inl _ _ φ.hs}, pushout.condition⟩
  ext X' X Y f₁ f₂ s hs eq := by
    refine ⟨_, cokernel.π (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_epi]
      exact (exists_isoModSerre_comp_eq_zero_iff P _).1 ⟨_, s, hs, by simpa [sub_eq_zero]⟩
    · simpa only [Preadditive.sub_comp, sub_eq_zero] using cokernel.condition (f₁ - f₂)

instance : P.isoModSerre.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ :=
    ⟨{s := pullback.fst φ.f φ.s
      f := pullback.snd φ.f φ.s,
      hs := MorphismProperty.pullback_fst _ _ φ.hs}, pullback.condition⟩
  ext X Y Y' f₁ f₂ s hs eq := by
    refine ⟨_, kernel.ι (f₁ - f₂), ?_, ?_⟩
    · rw [isoModSerre_iff_of_mono]
      exact P.prop_of_iso (Abelian.coimageIsoImage (f₁ - f₂)).symm
        ((exists_comp_isoModSerre_eq_zero_iff P _).1 ⟨_ ,s, hs, by simpa [sub_eq_zero]⟩)
    · simpa only [Preadditive.comp_sub, sub_eq_zero] using kernel.condition (f₁ - f₂)

noncomputable example : Preadditive P.isoModSerre.Localization := inferInstance

variable [L.IsLocalization P.isoModSerre] [Preadditive D] [L.Additive]

include L P

lemma isZero_obj_iff (X : C) :
    IsZero (L.obj X) ↔ P X := by
  sorry

lemma hasZeroObject : HasZeroObject D :=
  ⟨L.obj 0, by simpa [isZero_obj_iff L P] using P.prop_zero⟩

lemma mono_map_iff {X Y : C} (f : X ⟶ Y) :
    Mono (L.map f) ↔ P.monoModSerre f := by
  sorry

lemma epi_map_iff {X Y : C} (f : X ⟶ Y) :
    Epi (L.map f) ↔ P.epiModSerre f := by
  sorry

lemma preservesMonomorphisms : L.PreservesMonomorphisms where
  preserves f _ := by simpa only [mono_map_iff _ P] using P.monoModSerre_of_mono f

lemma preservesEpimorphisms : L.PreservesEpimorphisms where
  preserves f _ := by simpa only [epi_map_iff _ P] using P.epiModSerre_of_epi f

lemma preservesKernel {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) L := by
  have := preservesMonomorphisms L P
  refine preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
    ((KernelFork.isLimitMapConeEquiv _ L).2 ?_)
  sorry

lemma preservesCokernel {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) L := by
  have := preservesEpimorphisms L P
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ L).2 ?_)
  sorry

lemma hasKernels : HasKernels D where
  has_limit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesKernel L P g.hom
    have : HasLimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (KernelFork.isLimitMapConeEquiv _ L).1
        (isLimitOfPreserves L (kernelIsKernel g.hom))⟩
    exact hasLimit_of_iso (show parallelPair (L.map g.hom) 0 ≅ _ from
      parallelPair.ext (Arrow.leftFunc.mapIso e)
        (Arrow.rightFunc.mapIso e) (by cat_disch) (by cat_disch))

lemma hasCokernels : HasCokernels D where
  has_colimit f := by
    obtain ⟨g, ⟨e⟩⟩ :=
      (Localization.essSurj_mapArrow L P.isoModSerre).mem_essImage (Arrow.mk f)
    have := preservesCokernel L P g.hom
    have : HasColimit (parallelPair (L.map g.hom) 0) :=
      ⟨_, (CokernelCofork.isColimitMapCoconeEquiv _ L).1
        (isColimitOfPreserves L (cokernelIsCokernel g.hom))⟩
    exact hasColimit_of_iso (show _ ≅ parallelPair (L.map g.hom) 0 from
      parallelPair.ext (Arrow.leftFunc.mapIso e.symm)
        (Arrow.rightFunc.mapIso e.symm) (by cat_disch) (by cat_disch))

lemma hasEqualizers : HasEqualizers D :=
  have := hasKernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasEqualizer f g :=
    Preadditive.hasEqualizer_of_hasKernel _ _
  hasEqualizers_of_hasLimit_parallelPair _

lemma hasCoequalizers : HasCoequalizers D :=
  have := hasCokernels L P
  have {X Y : D} (f g : X ⟶ Y) : HasCoequalizer f g := by
    exact Preadditive.hasCoequalizer_of_hasCokernel _ _
  hasCoequalizers_of_hasColimit_parallelPair _

lemma hasBinaryProducts : HasBinaryProducts D := by
  have := Localization.essSurj L P.isoModSerre
  have (X Y : D) : HasBinaryProduct X Y :=
    hasLimit_of_iso (show Limits.pair _ _ ≅ _ from
      mapPairIso (L.objObjPreimageIso X) (L.objObjPreimageIso Y))
  exact hasBinaryProducts_of_hasLimit_pair D

lemma hasBinaryBiproducts : HasBinaryBiproducts D :=
  have := hasBinaryProducts L P
  .of_hasBinaryProducts

lemma hasBinaryCoproducts : HasBinaryCoproducts D :=
  have := hasBinaryBiproducts L P
  hasBinaryCoproducts_of_hasBinaryBiproducts

lemma hasFiniteProducts : HasFiniteProducts D :=
  have := hasZeroObject L P
  have := hasBinaryProducts L P
  hasFiniteProducts_of_has_binary_and_terminal

lemma hasFiniteLimits : HasFiniteLimits D :=
  have := hasEqualizers L P
  have := hasFiniteProducts L P
  hasFiniteLimits_of_hasEqualizers_and_finite_products

lemma hasFiniteCoproducts : HasFiniteCoproducts D :=
  have := hasZeroObject L P
  have := hasBinaryCoproducts L P
  hasFiniteCoproducts_of_has_binary_and_initial

lemma hasFiniteColimits : HasFiniteColimits D :=
  have := hasCoequalizers L P
  have := hasFiniteCoproducts L P
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

lemma mono_iff {X Y : D} (f : X ⟶ Y) :
    Mono f ↔ ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Mono f'),
      Nonempty (L.mapArrow.obj (Arrow.mk f') ≅ Arrow.mk f) := sorry

lemma epi_iff {X Y : D} (f : X ⟶ Y) :
    Epi f ↔ ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : Epi f'),
      Nonempty (L.mapArrow.obj (Arrow.mk f') ≅ Arrow.mk f) := sorry

lemma isNormalMonoCategory : IsNormalMonoCategory D where
  normalMonoOfMono f hf := by
    rw [mono_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalMonoOfMono f'
    refine ⟨NormalMono.ofArrowIso ?_ e⟩
    exact {
      Z := L.obj hf'.Z
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isLimit :=
        have := preservesKernel L P hf'.g
        (KernelFork.isLimitMapConeEquiv _ L).1
          (isLimitOfPreserves L hf'.isLimit) }

lemma isNormalEpiCategory : IsNormalEpiCategory D where
  normalEpiOfEpi f hf := by
    rw [epi_iff L P] at hf
    obtain ⟨X', Y', f', _, ⟨e⟩⟩ := hf
    let hf' := normalEpiOfEpi f'
    refine ⟨NormalEpi.ofArrowIso ?_ e⟩
    exact {
      W := L.obj hf'.W
      g := L.map hf'.g
      w := by rw [← L.map_comp]; simp [hf'.w]
      isColimit :=
        have := preservesCokernel L P hf'.g
        (CokernelCofork.isColimitMapCoconeEquiv _ L).1
          (isColimitOfPreserves L hf'.isColimit) }

def abelian : Abelian D := by
  have := hasFiniteProducts L P
  have := hasKernels L P
  have := hasCokernels L P
  have := isNormalMonoCategory L P
  have := isNormalEpiCategory L P
  constructor

lemma preservesFiniteLimits : PreservesFiniteLimits L := by
  letI := abelian L P
  have := (Functor.preservesFiniteLimits_tfae L).out 3 2
  rw [this]
  intro _ _ f
  exact preservesKernel L P f

lemma preservesFiniteColimits : PreservesFiniteColimits L := by
  letI := abelian L P
  have := (Functor.preservesFiniteColimits_tfae L).out 3 2
  rw [this]
  intro _ _ f
  exact preservesCokernel L P f

end SerreClassLocalization

end ObjectProperty

end CategoryTheory
