/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The action of a left/right exact functors on homology

-/

universe v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ShortComplex

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

variable (S S' : ShortComplex C) (φ : S ⟶ S') (F : C ⥤ D) [F.PreservesZeroMorphisms]
  [S.HasHomology] [(S.map F).HasHomology]
  [S'.HasHomology] [(S'.map F).HasHomology]

/-- The morphism `F.obj S.cycles ⟶ (S.map F).cycles` when `S : ShortComplex C`
and `F : C ⥤ D`. -/
noncomputable def mapCycles : F.obj S.cycles ⟶ (S.map F).cycles :=
  (S.map F).liftCycles (F.map S.iCycles) (by
    dsimp
    rw [← F.map_comp, iCycles_g, Functor.map_zero])

@[reassoc (attr := simp)]
lemma mapCycles_i : S.mapCycles F ≫ (S.map F).iCycles = F.map S.iCycles := by
  simp [mapCycles]

variable {S S'} in
@[reassoc (attr := simp)]
lemma mapCycles_naturality [(F.mapShortComplex.obj S').HasHomology] :
    S.mapCycles F ≫ cyclesMap (F.mapShortComplex.map φ) =
      F.map (cyclesMap φ) ≫ S'.mapCycles F := by
  simp [← cancel_mono (S'.map F).iCycles, ← F.map_comp (cyclesMap φ)]

@[reassoc (attr := simp)]
lemma map_toCycles_mapCycles :
    F.map S.toCycles ≫ S.mapCycles F = (S.map F).toCycles := by
  simp [← cancel_mono (S.map F).iCycles, ← F.map_comp]

/-- The morphism `(S.map F).opcycles ⟶ F.obj S.opcycles` when `S : ShortComplex C`
and `F : C ⥤ D`. -/
noncomputable def mapOpcycles : (S.map F).opcycles ⟶ F.obj S.opcycles :=
  (S.map F).descOpcycles (F.map S.pOpcycles) (by
    dsimp
    rw [← F.map_comp, f_pOpcycles, Functor.map_zero])

@[reassoc (attr := simp)]
lemma p_mapOpcycles : (S.map F).pOpcycles ≫ S.mapOpcycles F = F.map S.pOpcycles := by
  simp [mapOpcycles]

variable {S S'} in
@[reassoc (attr := simp)]
lemma mapOpcycles_naturality [(F.mapShortComplex.obj S).HasHomology]
    [(F.mapShortComplex.obj S').HasHomology] :
    opcyclesMap (F.mapShortComplex.map φ) ≫ S'.mapOpcycles F  =
      S.mapOpcycles F ≫ F.map (opcyclesMap φ) := by
  simp [← cancel_epi (S.map F).pOpcycles, ← F.map_comp S.pOpcycles]

@[reassoc (attr := simp)]
lemma mapOpcycles_map_fromOpcycles :
    S.mapOpcycles F ≫ F.map S.fromOpcycles = (S.map F).fromOpcycles := by
  simp [← cancel_epi (S.map F).pOpcycles, ← F.map_comp]

lemma isIso_mapCycles_iff :
    IsIso (S.mapCycles F) ↔ PreservesLimit (parallelPair S.g 0) F := by
  constructor
  · intro
    exact preservesLimit_of_preserves_limit_cone S.cyclesIsKernel
      ((KernelFork.isLimitMapConeEquiv _ _).2
      (IsLimit.ofIsoLimit (S.map F).cyclesIsKernel
      (Fork.ext (asIso (S.mapCycles F))).symm))
  · intro
    exact (IsLimit.conePointUniqueUpToIso
      (KernelFork.mapIsLimit _ S.cyclesIsKernel F) (S.map F).cyclesIsKernel).isIso_hom

instance [PreservesLimit (parallelPair S.g 0) F] : IsIso (S.mapCycles F) := by
  rwa [isIso_mapCycles_iff]

lemma isIso_mapOpcycles_iff :
    IsIso (S.mapOpcycles F) ↔ PreservesColimit (parallelPair S.f 0) F := by
  constructor
  · intro
    exact preservesColimit_of_preserves_colimit_cocone S.opcyclesIsCokernel
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).2
      (IsColimit.ofIsoColimit (S.map F).opcyclesIsCokernel
      (Cofork.ext (asIso (S.mapOpcycles F)))))
  · intro
    exact (IsColimit.coconePointUniqueUpToIso (S.map F).opcyclesIsCokernel
      (CokernelCofork.mapIsColimit _ S.opcyclesIsCokernel F)).isIso_hom

instance [PreservesColimit (parallelPair S.f 0) F] : IsIso (S.mapOpcycles F) := by
  rwa [isIso_mapOpcycles_iff]

/-- Given `S : ShortComplex C` and `F : C ⥤ D`, this is the canonical
morphism `F.obj S.homology ⟶ (S.map F).homology` when `F` preserves
the cokernel of `S.toCycles : S.X₁ ⟶ S.toCycles`. -/
noncomputable def mapHomologyOfPreservesCokernel
    [PreservesColimit (parallelPair S.toCycles 0) F] :
    F.obj S.homology ⟶ (S.map F).homology :=
  (CokernelCofork.mapIsColimit _ (S.homologyIsCokernel) F).desc
    (CokernelCofork.ofπ (S.mapCycles F ≫ (S.map F).homologyπ) (by simp))

@[reassoc (attr := simp)]
lemma map_toCycles_mapHomologyOfPreservesCokernel
    [PreservesColimit (parallelPair S.toCycles 0) F] :
    F.map S.homologyπ ≫ S.mapHomologyOfPreservesCokernel F =
      S.mapCycles F ≫ (S.map F).homologyπ :=
  (CokernelCofork.mapIsColimit _ (S.homologyIsCokernel) F).fac _ .one

variable {S S'} in
@[reassoc (attr := simp)]
lemma mapHomologyOfPreservesColernel_naturality
    [PreservesColimit (parallelPair S.toCycles 0) F]
    [PreservesColimit (parallelPair S'.toCycles 0) F]
    [(F.mapShortComplex.obj S).HasHomology]
    [(F.mapShortComplex.obj S').HasHomology] :
      S.mapHomologyOfPreservesCokernel F ≫ homologyMap (F.mapShortComplex.map φ) =
    F.map (homologyMap φ) ≫ S'.mapHomologyOfPreservesCokernel F := by
  have : Epi (F.map S.homologyπ) := sorry
  simp [← cancel_epi (F.map S.homologyπ), ← F.map_comp_assoc]

/-- Given `S : ShortComplex C` and `F : C ⥤ D`, this is the canonical
morphism `(S.map F).homology ⟶ F.obj S.homology` when `F` preserves
the kernel of `S.fromOpcycles : S.opcycles ⟶ S.X₃`. -/
noncomputable def mapHomologyOfPreservesKernel
    [PreservesLimit (parallelPair S.fromOpcycles 0) F] :
    (S.map F).homology ⟶ F.obj S.homology :=
  (KernelFork.mapIsLimit _ (S.homologyIsKernel) F).lift
    (KernelFork.ofι ((S.map F).homologyι ≫ S.mapOpcycles F) (by simp))

@[reassoc (attr := simp)]
lemma mapHomologyOfPreservesKernel_map_fromOpcycles
    [PreservesLimit (parallelPair S.fromOpcycles 0) F] :
    S.mapHomologyOfPreservesKernel F ≫ F.map S.homologyι =
      (S.map F).homologyι ≫ S.mapOpcycles F :=
  (KernelFork.mapIsLimit _ (S.homologyIsKernel) F).fac _ .zero

variable {S S'} in
@[reassoc (attr := simp)]
lemma mapHomologyOfPreservesKernel_naturality
    [PreservesLimit (parallelPair S.fromOpcycles 0) F]
    [PreservesLimit (parallelPair S'.fromOpcycles 0) F]
    [(F.mapShortComplex.obj S).HasHomology]
    [(F.mapShortComplex.obj S').HasHomology] :
      homologyMap (F.mapShortComplex.map φ) ≫ S'.mapHomologyOfPreservesKernel F =
    S.mapHomologyOfPreservesKernel F ≫ F.map (homologyMap φ) := by
  have : Mono (F.map S'.homologyι) := sorry
  simp [← cancel_mono (F.map S'.homologyι), ← F.map_comp (homologyMap φ)]

lemma mapCycles_eq_mapCyclesIso_inv [F.PreservesLeftHomologyOf S] :
    S.mapCycles F = (S.mapCyclesIso F).inv := by
  simp [← cancel_mono (S.map F).iCycles, ← cancel_epi (S.mapCyclesIso F).hom]

lemma mapOpcycles_eq_mapOpcyclesIso_hom [F.PreservesRightHomologyOf S] :
    S.mapOpcycles F = (S.mapOpcyclesIso F).hom := by
  simp [← cancel_epi (S.map F).pOpcycles, ← cancel_mono (S.mapOpcyclesIso F).inv]

end

variable [Abelian C] [Abelian D]
  (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma mapHomologyIso_hom_eq_mapHomologyOfPreservesKernel :
    (S.mapHomologyIso F).hom = S.mapHomologyOfPreservesKernel F := by
  rw [← cancel_epi (S.map F).homologyπ, homologyπ_mapHomologyIso_hom,
    ← cancel_mono (F.map S.homologyι), assoc, assoc, ← F.map_comp,
    homology_π_ι, mapHomologyOfPreservesKernel_map_fromOpcycles,
    F.map_comp, mapCyclesIso_hom_iCycles_assoc, homology_π_ι_assoc,
    p_mapOpcycles]

lemma mapHomologyIso_inv_eq_mapHomologyOfPreservesCokernel :
    (S.mapHomologyIso F).inv = S.mapHomologyOfPreservesCokernel F := by
  rw [← cancel_mono (S.map F).homologyι, ← mapHomologyIso'_eq_mapHomologyIso,
    mapHomologyIso'_hom_homologyι, ← cancel_epi (F.map S.homologyπ),
    ← F.map_comp_assoc, homology_π_ι,
    F.map_comp_assoc, pOpcycles_mapOpcyclesIso_hom,
    map_toCycles_mapHomologyOfPreservesCokernel_assoc,
    homology_π_ι, mapCycles_i_assoc]

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [Abelian C] [Abelian D] [F.Additive]

/-- The natural transformation `F.obj S.cycles ⟶ (S.map F).cycles`. -/
@[simps]
noncomputable def mapCyclesNatTrans :
    ShortComplex.cyclesFunctor C ⋙ F ⟶
  F.mapShortComplex ⋙ ShortComplex.cyclesFunctor D where
  app S := S.mapCycles F

/-- The natural transformation `(S.map F).opcycles ⟶ F.obj S.opcycles`. -/
@[simps]
noncomputable def mapOpcyclesNatTrans :
    F.mapShortComplex ⋙ ShortComplex.opcyclesFunctor D ⟶
      ShortComplex.opcyclesFunctor C ⋙ F where
  app S := S.mapOpcycles F

/-- The natural transformation `(S.map F).homology ⟶ F.obj S.homology`
when `F` is left exact. -/
noncomputable def mapHomologyNatTransOfPreservesFiniteLimits [PreservesFiniteLimits F] :
    F.mapShortComplex ⋙ ShortComplex.homologyFunctor D ⟶
      ShortComplex.homologyFunctor C ⋙ F where
  app S := S.mapHomologyOfPreservesKernel F

/-- The natural transformation `F.obj S.homology ⟶ (S.map F).homology`
when `F` is right exact. -/
noncomputable def mapHomologyNatTransOfPreservesFiniteColimits [PreservesFiniteColimits F] :
    ShortComplex.homologyFunctor C ⋙ F ⟶
    F.mapShortComplex ⋙ ShortComplex.homologyFunctor D where
  app S := S.mapHomologyOfPreservesCokernel F

end Functor

end CategoryTheory
