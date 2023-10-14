/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Functors which preserves homology

If `F : C ⥤ D` is a functor between categories with zero morphisms, we shall
say that `F` preserves homology when `F` preserves both kernels and cokernels.
This typeclass is named `[F.PreservesHomology]`, and is automatically
satisfied when `F` preserves both finite limits and finite colimits.

TODO: If `S : ShortComplex C` and `[F.PreservesHomology]`, then there is an
isomorphism `S.mapHomologyIso F : (S.map F).homology ≅ F.obj S.homology`.

-/

namespace CategoryTheory

open Category Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

variable (F : C ⥤ D)

/-- A functor preserves homology when it preserves both kernels and cokernels. -/
class PreservesHomology (F : C ⥤ D) [PreservesZeroMorphisms F] where
  /-- the functor preserves kernels -/
  preservesKernels ⦃X Y : C⦄ (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F :=
    by infer_instance
  /-- the functor preserves cokernels -/
  preservesCokernels ⦃X Y : C⦄ (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) F :=
    by infer_instance

variable [PreservesZeroMorphisms F]

/-- A functor which preserves homology preserves kernels. -/
def PreservesHomology.preservesKernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) F :=
  PreservesHomology.preservesKernels _

/-- A functor which preserves homology preserves cokernels. -/
def PreservesHomology.preservesCokernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) F :=
  PreservesHomology.preservesCokernels _

noncomputable instance preservesHomologyOfExact
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
  F.PreservesHomology where

end Functor

namespace ShortComplex

variable {S S₁ S₂ : ShortComplex C}

namespace LeftHomologyData

variable (h : S.LeftHomologyData) (F : C ⥤ D)

/-- A left homology data `h` of a short complex `S` is preserved by a functor `F` is
`F` preserves the kernel of `S.g : S.X₂ ⟶ S.X₃` and the cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
class IsPreservedBy [F.PreservesZeroMorphisms] where
  /-- the functor preserves the kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
  g : PreservesLimit (parallelPair S.g 0) F
  /-- the functor preserves the cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
  f' : PreservesColimit (parallelPair h.f' 0) F

variable [F.PreservesZeroMorphisms]

noncomputable instance isPreservedByOfPreservesHomology [F.PreservesHomology] :
    h.IsPreservedBy F where
  g := Functor.PreservesHomology.preservesKernel _ _
  f' := Functor.PreservesHomology.preservesCokernel _ _

variable [h.IsPreservedBy F]

/-- When a left homology data is preserved by a functor `F`, this functor
preserves the kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
def IsPreservedBy.hg : PreservesLimit (parallelPair S.g 0) F :=
  @IsPreservedBy.g _ _ _ _ _ _ _ h F _ _

/-- When a left homology data `h` is preserved by a functor `F`, this functor
preserves the cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
def IsPreservedBy.hf' : PreservesColimit (parallelPair h.f' 0) F := IsPreservedBy.f'

/-- When a left homology data `h` of a short complex `S` is preserved by a functor `F`,
this is the induced left homology data `h.map F` for the short complex `S.map F`. -/
@[simps]
noncomputable def map : (S.map F).LeftHomologyData := by
  have := IsPreservedBy.hg h F
  have := IsPreservedBy.hf' h F
  have wi : F.map h.i ≫ F.map S.g = 0 := by rw [← F.map_comp, h.wi, F.map_zero]
  have hi := KernelFork.mapIsLimit _ h.hi F
  let f' : F.obj S.X₁ ⟶ F.obj h.K := hi.lift (KernelFork.ofι (S.map F).f (S.map F).zero)
  have hf' : f' = F.map h.f' := Fork.IsLimit.hom_ext hi (by
    rw [Fork.IsLimit.lift_ι hi]
    simp only [KernelFork.map_ι, Fork.ι_ofι, map_f, ← F.map_comp, f'_i])
  have wπ : f' ≫ F.map h.π = 0 := by rw [hf', ← F.map_comp, f'_π, F.map_zero]
  have hπ : IsColimit (CokernelCofork.ofπ (F.map h.π) wπ) := by
    let e : parallelPair f' 0 ≅ parallelPair (F.map h.f') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hf') (by simp)
    refine' IsColimit.precomposeInvEquiv e _
      (IsColimit.ofIsoColimit (CokernelCofork.mapIsColimit _ h.hπ' F) _)
    exact Cofork.ext (Iso.refl _) (by simp)
  exact
    { K := F.obj h.K
      H := F.obj h.H
      i := F.map h.i
      π := F.map h.π
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hπ }

@[simp]
lemma map_f' : (h.map F).f' = F.map h.f' := by
  rw [← cancel_mono (h.map F).i, f'_i, map_f, map_i, ← F.map_comp, f'_i]

end LeftHomologyData

/-- Given a left homology map data `ψ : LeftHomologyMapData φ h₁ h₂` such that
both left homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced left homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
def LeftHomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
    {h₂ : S₂.LeftHomologyData} (ψ : LeftHomologyMapData φ h₁ h₂) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h₁.IsPreservedBy F] [h₂.IsPreservedBy F] :
    LeftHomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  φK := F.map ψ.φK
  φH := F.map ψ.φH
  commi := by simpa only [F.map_comp] using F.congr_map ψ.commi
  commf' := by simpa only [LeftHomologyData.map_f', F.map_comp] using F.congr_map ψ.commf'
  commπ := by simpa only [F.map_comp] using F.congr_map ψ.commπ

namespace RightHomologyData

variable (h : S.RightHomologyData) (F : C ⥤ D)

/-- A right homology data `h` of a short complex `S` is preserved by a functor `F` is
`F` preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂` and the kernel of `h.g' : h.Q ⟶ S.X₃`. -/
class IsPreservedBy [F.PreservesZeroMorphisms] where
  /-- the functor preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
  f : PreservesColimit (parallelPair S.f 0) F
  /-- the functor preserves the kernel of `h.g' : h.Q ⟶ S.X₃`. -/
  g' : PreservesLimit (parallelPair h.g' 0) F

variable [F.PreservesZeroMorphisms]

noncomputable instance isPreservedByOfPreservesHomology [F.PreservesHomology] :
    h.IsPreservedBy F where
  f := Functor.PreservesHomology.preservesCokernel F _
  g' := Functor.PreservesHomology.preservesKernel F _

variable [h.IsPreservedBy F]

/-- When a right homology data is preserved by a functor `F`, this functor
preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
def IsPreservedBy.hf : PreservesColimit (parallelPair S.f 0) F :=
  @IsPreservedBy.f _ _ _ _ _ _ _ h F _ _

/-- When a right homology data `h` is preserved by a functor `F`, this functor
preserves the kernel of `h.g' : h.Q ⟶ S.X₃`. -/
def IsPreservedBy.hg' : PreservesLimit (parallelPair h.g' 0) F :=
  @IsPreservedBy.g' _ _ _ _ _ _ _ h F _ _

/-- When a right homology data `h` of a short complex `S` is preserved by a functor `F`,
this is the induced right homology data `h.map F` for the short complex `S.map F`. -/
@[simps]
noncomputable def map : (S.map F).RightHomologyData := by
  have := IsPreservedBy.hf h F
  have := IsPreservedBy.hg' h F
  have wp : F.map S.f ≫ F.map h.p = 0 := by rw [← F.map_comp, h.wp, F.map_zero]
  have hp := CokernelCofork.mapIsColimit _ h.hp F
  let g' : F.obj h.Q ⟶ F.obj S.X₃ := hp.desc (CokernelCofork.ofπ (S.map F).g (S.map F).zero)
  have hg' : g' = F.map h.g' := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc hp]
    simp only [Cofork.π_ofπ, CokernelCofork.map_π, map_g, ← F.map_comp, p_g']
  have wι : F.map h.ι ≫ g' = 0 := by rw [hg', ← F.map_comp, ι_g', F.map_zero]
  have hι : IsLimit (KernelFork.ofι (F.map h.ι) wι) := by
    let e : parallelPair g' 0 ≅ parallelPair (F.map h.g') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hg') (by simp)
    refine' IsLimit.postcomposeHomEquiv e _
      (IsLimit.ofIsoLimit (KernelFork.mapIsLimit _ h.hι' F) _)
    exact Fork.ext (Iso.refl _) (by simp)
  exact
    { Q := F.obj h.Q
      H := F.obj h.H
      p := F.map h.p
      ι := F.map h.ι
      wp := wp
      hp := hp
      wι := wι
      hι := hι }

@[simp]
lemma map_g' : (h.map F).g' = F.map h.g' := by
  rw [← cancel_epi (h.map F).p, p_g', map_g, map_p, ← F.map_comp, p_g']

end RightHomologyData

/-- Given a right homology map data `ψ : RightHomologyMapData φ h₁ h₂` such that
both right homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced right homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
def RightHomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} (ψ : RightHomologyMapData φ h₁ h₂) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h₁.IsPreservedBy F] [h₂.IsPreservedBy F] :
    RightHomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  φQ := F.map ψ.φQ
  φH := F.map ψ.φH
  commp := by simpa only [F.map_comp] using F.congr_map ψ.commp
  commg' := by simpa only [RightHomologyData.map_g', F.map_comp] using F.congr_map ψ.commg'
  commι := by simpa only [F.map_comp] using F.congr_map ψ.commι

/-- When a homology data `h` of a short complex `S` is such that both `h.left` and
`h.right` are preserved by a functor `F`, this is the induced homology data
`h.map F` for the short complex `S.map F`. -/
@[simps]
noncomputable def HomologyData.map (h : S.HomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.left.IsPreservedBy F] [h.right.IsPreservedBy F] :
    (S.map F).HomologyData where
  left := h.left.map F
  right := h.right.map F
  iso := F.mapIso h.iso
  comm := by simpa only [F.map_comp] using F.congr_map h.comm

/-- Given a homology map data `ψ : HomologyMapData φ h₁ h₂` such that
`h₁.left`, `h₁.right`, `h₂.left` and `h₂.right` are all preserved by a functor `F`, this is
the induced homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
def HomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h₁.left.IsPreservedBy F] [h₁.right.IsPreservedBy F]
    [h₂.left.IsPreservedBy F] [h₂.right.IsPreservedBy F] :
    HomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  left := ψ.left.map F
  right := ψ.right.map F

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [PreservesZeroMorphisms F] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/-- A functor preserves the left homology of a short complex `S` if it preserves all the
left homology data of `S`. -/
class PreservesLeftHomologyOf where
  /-- the functor preserves all the left homology data of the short complex -/
  isPreservedBy : ∀ (h : S.LeftHomologyData), h.IsPreservedBy F

/-- A functor preserves the right homology of a short complex `S` if it preserves all the
right homology data of `S`. -/
class PreservesRightHomologyOf where
  /-- the functor preserves all the right homology data of the short complex -/
  isPreservedBy : ∀ (h : S.RightHomologyData), h.IsPreservedBy F

noncomputable instance PreservesHomology.preservesLeftHomologyOf [F.PreservesHomology] :
    F.PreservesLeftHomologyOf S := ⟨inferInstance⟩

noncomputable instance PreservesHomology.preservesRightHomologyOf [F.PreservesHomology] :
    F.PreservesRightHomologyOf S := ⟨inferInstance⟩

variable {S}

/-- If a functor preserves a certain left homology data of a short complex `S`, then it
preserves the left homology of `S`. -/
def PreservesLeftHomologyOf.mk' (h : S.LeftHomologyData) [h.IsPreservedBy F] :
    F.PreservesLeftHomologyOf S where
  isPreservedBy h' :=
    { g := ShortComplex.LeftHomologyData.IsPreservedBy.hg h F
      f' := by
        have := ShortComplex.LeftHomologyData.IsPreservedBy.hf' h F
        let e : parallelPair h.f' 0 ≅ parallelPair h'.f' 0 :=
          parallelPair.ext (Iso.refl _) (ShortComplex.cyclesMapIso' (Iso.refl S) h h')
            (by simp) (by simp)
        exact preservesColimitOfIsoDiagram F e }

/-- If a functor preserves a certain right homology data of a short complex `S`, then it
preserves the right homology of `S`. -/
def PreservesRightHomologyOf.mk' (h : S.RightHomologyData) [h.IsPreservedBy F] :
    F.PreservesRightHomologyOf S where
  isPreservedBy h' :=
    { f := ShortComplex.RightHomologyData.IsPreservedBy.hf h F
      g' := by
        have := ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
        let e : parallelPair h.g' 0 ≅ parallelPair h'.g' 0 :=
          parallelPair.ext (ShortComplex.opcyclesMapIso' (Iso.refl S) h h') (Iso.refl _)
            (by simp) (by simp)
        exact preservesLimitOfIsoDiagram F e }

end Functor

namespace ShortComplex

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

instance LeftHomologyData.isPreservedByOfPreserves [F.PreservesLeftHomologyOf S] :
    h₁.IsPreservedBy F :=
  Functor.PreservesLeftHomologyOf.isPreservedBy _

instance RightHomologyData.isPreservedByOfPreserves [F.PreservesRightHomologyOf S] :
    h₂.IsPreservedBy F :=
  Functor.PreservesRightHomologyOf.isPreservedBy _

variable (S)

instance hasLeftHomology_of_preserves [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).HasLeftHomology :=
  HasLeftHomology.mk' (S.leftHomologyData.map F)

instance hasLeftHomology_of_preserves' [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (F.mapShortComplex.obj S).HasLeftHomology :=
  by dsimp; infer_instance

instance hasRightHomology_of_preserves [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).HasRightHomology :=
  HasRightHomology.mk' (S.rightHomologyData.map F)

instance hasRightHomology_of_preserves' [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (F.mapShortComplex.obj S).HasRightHomology :=
  by dsimp; infer_instance

instance hasHomology_of_preserves [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    (S.map F).HasHomology :=
  HasHomology.mk' (S.homologyData.map F)

instance hasHomology_of_preserves' [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    (F.mapShortComplex.obj S).HasHomology :=
  by dsimp; infer_instance

end ShortComplex

end CategoryTheory
