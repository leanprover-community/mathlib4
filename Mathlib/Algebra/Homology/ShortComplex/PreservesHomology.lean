import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

namespace CategoryTheory

open Category Limits ZeroObject

variable {C D : Type _} [Category C] [Category D]

namespace Functor

variable (F : C ⥤ D)

class PreservesHomology (F : C ⥤ D) [HasZeroMorphisms C] [HasZeroMorphisms D]
  [PreservesZeroMorphisms F] where
  preserves_kernels : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F :=
    by infer_instance
  preserves_cokernels : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F :=
    by infer_instance

def PreservesHomology.preserves_kernel (F : C ⥤ D) [HasZeroMorphisms C] [HasZeroMorphisms D]
    [PreservesZeroMorphisms F] [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) F :=
  PreservesHomology.preserves_kernels _

def PreservesHomology.preserves_cokernel (F : C ⥤ D) [HasZeroMorphisms C] [HasZeroMorphisms D]
    [PreservesZeroMorphisms F] [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) F :=
  PreservesHomology.preserves_cokernels _

noncomputable instance preservesHomologyOfExact [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
  F.PreservesHomology where
  preserves_kernels := inferInstance
  preserves_cokernels := inferInstance

end Functor

namespace ShortComplex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] {S S₁ S₂ : ShortComplex C}

namespace LeftHomologyData

class IsPreservedBy (h : S.LeftHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms] where
  g : PreservesLimit (parallelPair S.g 0) F
  f' : PreservesColimit (parallelPair h.f' 0) F

def IsPreservedBy.hg (h : S.LeftHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.IsPreservedBy F] : PreservesLimit (parallelPair S.g 0) F :=
  @IsPreservedBy.g _ _ _ _ _ _ _ h F _ _

def IsPreservedBy.hf' (h : S.LeftHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.IsPreservedBy F] : PreservesColimit (parallelPair h.f' 0) F :=
  @IsPreservedBy.f' _ _ _ _ _ _ _ h F _ _

noncomputable instance isPreservedByOfPreservesHomology (h : S.LeftHomologyData) (F : C ⥤ D)
  [F.PreservesZeroMorphisms] [F.PreservesHomology] : h.IsPreservedBy F where
  g := Functor.PreservesHomology.preserves_kernel F _
  f' := Functor.PreservesHomology.preserves_cokernel F _

section

variable (h : S.LeftHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms] [h.IsPreservedBy F]

@[simps]
noncomputable def map : (S.map F).LeftHomologyData := by
  have := IsPreservedBy.hg h F
  have := IsPreservedBy.hf' h F
  have wi : F.map h.i ≫ F.map S.g = 0 := by rw [← F.map_comp, h.wi, F.map_zero]
  have hi := KernelFork.mapIsLimit _ h.hi F
  let f' : F.obj S.X₁ ⟶ F.obj h.K := hi.lift (KernelFork.ofι (S.map F).f (S.map F).zero)
  have hf' : f' = F.map h.f' := by
    apply Fork.IsLimit.hom_ext hi
    rw [Fork.IsLimit.lift_ι hi]
    simp only [KernelFork.map_ι, Fork.ι_ofι, map_f, ← F.map_comp, f'_i]
  have wπ : f' ≫ F.map h.π = 0 := by rw [hf', ← F.map_comp, f'_π, F.map_zero]
  have hπ : IsColimit (CokernelCofork.ofπ (F.map h.π) wπ) := by
    let e : parallelPair f' 0 ≅ parallelPair (F.map h.f') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hf') (by simp)
    refine' IsColimit.precomposeInvEquiv e _
      (IsColimit.ofIsoColimit (CokernelCofork.mapIsColimit _ h.hπ' F) _)
    refine' Cocones.ext (Iso.refl _) _
    rintro (_|_)
    . simp [← hf']
    . simp
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

end

end LeftHomologyData

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

class IsPreservedBy (h : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms] where
  f : PreservesColimit (parallelPair S.f 0) F
  g' : PreservesLimit (parallelPair h.g' 0) F

def IsPreservedBy.hf (h : S.RightHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.IsPreservedBy F] : PreservesColimit (parallelPair S.f 0) F :=
  @IsPreservedBy.f _ _ _ _ _ _ _ h F _ _

def IsPreservedBy.hg' (h : S.RightHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.IsPreservedBy F] : PreservesLimit (parallelPair h.g' 0) F :=
  @IsPreservedBy.g' _ _ _ _ _ _ _ h F _ _

noncomputable instance isPreservedByOfPreservesHomology (h : S.RightHomologyData) (F : C ⥤ D)
  [F.PreservesZeroMorphisms] [F.PreservesHomology] : h.IsPreservedBy F where
  f := Functor.PreservesHomology.preserves_cokernel F _
  g' := Functor.PreservesHomology.preserves_kernel F _

section

variable (h : S.RightHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms] [h.IsPreservedBy F]

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
    refine' Cones.ext (Iso.refl _) _
    rintro (_|_)
    . simp
    . simp [← hg']
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

end

end RightHomologyData

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

@[simps]
noncomputable def HomologyData.map (h : S.HomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.left.IsPreservedBy F] [h.right.IsPreservedBy F] :
    (S.map F).HomologyData where
  left := h.left.map F
  right := h.right.map F
  iso := F.mapIso h.iso
  comm := by simpa only [F.map_comp] using F.congr_map h.comm

@[simps]
def HomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData}
    {h₂ : S₂.HomologyData} (ψ : HomologyMapData φ h₁ h₂) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h₁.left.IsPreservedBy F] [h₁.right.IsPreservedBy F]
    [h₂.left.IsPreservedBy F] [h₂.right.IsPreservedBy F] :
    HomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  left := ψ.left.map F
  right := ψ.right.map F

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [HasZeroMorphisms C] [HasZeroMorphisms D]
  [PreservesZeroMorphisms F] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

class PreservesLeftHomologyOf where
  condition' : ∀ (h : S.LeftHomologyData), h.IsPreservedBy F

class PreservesRightHomologyOf where
  condition' : ∀ (h : S.RightHomologyData), h.IsPreservedBy F

instance PreservesLeftHomologyOf.condition (h : S.LeftHomologyData)
    [F.PreservesLeftHomologyOf S] : h.IsPreservedBy F :=
  PreservesLeftHomologyOf.condition' _

instance PreservesRightHomologyOf.condition (h : S.RightHomologyData)
    [F.PreservesRightHomologyOf S] : h.IsPreservedBy F :=
  PreservesRightHomologyOf.condition' _

instance hasLeftHomology_of_preservesLeftHomologyOf
    [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] : (S.map F).HasLeftHomology :=
  ShortComplex.HasLeftHomology.mk' (S.leftHomologyData.map F)

instance hasRightHomology_of_preservesRightHomologyOf
    [S.HasRightHomology] [F.PreservesRightHomologyOf S] : (S.map F).HasRightHomology :=
  ShortComplex.HasRightHomology.mk' (S.rightHomologyData.map F)

instance hasLeftHomology_of_preservesLeftHomology_of'
    [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (F.mapShortComplex.obj S).HasLeftHomology :=
  hasLeftHomology_of_preservesLeftHomologyOf F S

instance hasRightHomology_of_preservesRightHomology_of'
    [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (F.mapShortComplex.obj S).HasRightHomology :=
  hasRightHomology_of_preservesRightHomologyOf F S

instance hasHomology_of_preservesLeftRightHomologyOf
    [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] : (S.map F).HasHomology :=
  ShortComplex.HasHomology.mk' (S.homologyData.map F)

instance hasHomology_of_preservesLeftRightHomologyOf'
    [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] : (F.mapShortComplex.obj S).HasHomology :=
  hasHomology_of_preservesLeftRightHomologyOf F S

noncomputable instance PreservesHomology.preservesLeftHomologyOf [F.PreservesHomology] :
    F.PreservesLeftHomologyOf S := ⟨fun _ => inferInstance⟩

noncomputable instance PreservesHomology.preservesRightHomologyOf [F.PreservesHomology] :
    F.PreservesRightHomologyOf S := ⟨fun _ => inferInstance⟩

variable {S}

def preservesLeftHomologyOf_of_leftHomologyData_isPreservedBy (h : S.LeftHomologyData)
    [h.IsPreservedBy F] : F.PreservesLeftHomologyOf S := ⟨fun h' =>
  { g := ShortComplex.LeftHomologyData.IsPreservedBy.hg h F
    f' := by
      let e : parallelPair h.f' 0 ≅ parallelPair h'.f' 0 :=
        parallelPair.ext (Iso.refl _) (ShortComplex.cyclesMapIso' (Iso.refl S) h h')
          (by simp) (by simp)
      have := ShortComplex.LeftHomologyData.IsPreservedBy.hf' h F
      exact preservesColimitOfIsoDiagram F e }⟩

def preservesRightHomologyOf_of_rightHomologyData_isPreservedBy (h : S.RightHomologyData)
    [h.IsPreservedBy F] : F.PreservesRightHomologyOf S := ⟨fun h' =>
  { f := ShortComplex.RightHomologyData.IsPreservedBy.hf h F
    g' := by
      let e : parallelPair h.g' 0 ≅ parallelPair h'.g' 0 :=
        parallelPair.ext (ShortComplex.opcyclesMapIso' (Iso.refl S) h h') (Iso.refl _)
          (by simp) (by simp)
      have := ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
      exact preservesLimitOfIsoDiagram F e }⟩

end Functor

namespace ShortComplex

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C)
  (hl : S.LeftHomologyData) (hr : S.RightHomologyData)
  {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  (hl₁ : S₁.LeftHomologyData) (hr₁ : S₁.RightHomologyData)
  (hl₂ : S₂.LeftHomologyData) (hr₂ : S₂.RightHomologyData)
  (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)
  (ψl : LeftHomologyMapData φ hl₁ hl₂)
  (ψr : RightHomologyMapData φ hr₁ hr₂)
  (F G : C ⥤ D) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

namespace LeftHomologyData

variable [hl₁.IsPreservedBy F] [hl₂.IsPreservedBy F]

lemma map_cyclesMap' : F.map (ShortComplex.cyclesMap' φ hl₁ hl₂) =
    ShortComplex.cyclesMap' (F.mapShortComplex.map φ) (hl₁.map F) (hl₂.map F) := by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.cyclesMap'_eq, (γ.map F).cyclesMap'_eq,  ShortComplex.LeftHomologyMapData.map_φK]

lemma map_leftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) =
    ShortComplex.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F) (hl₂.map F) := by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.leftHomologyMap'_eq, (γ.map F).leftHomologyMap'_eq,
    ShortComplex.LeftHomologyMapData.map_φH]

end LeftHomologyData

namespace RightHomologyData

variable [hr₁.IsPreservedBy F] [hr₂.IsPreservedBy F]

lemma map_opcyclesMap' : F.map (ShortComplex.opcyclesMap' φ hr₁ hr₂) =
    ShortComplex.opcyclesMap' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F) := by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.opcyclesMap'_eq, (γ.map F).opcyclesMap'_eq,  ShortComplex.RightHomologyMapData.map_φQ]

lemma map_rightHomologyMap' : F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) =
    ShortComplex.rightHomologyMap' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F) := by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.rightHomologyMap'_eq, (γ.map F).rightHomologyMap'_eq,
    ShortComplex.RightHomologyMapData.map_φH]

end RightHomologyData

lemma HomologyData.map_homologyMap'
    [h₁.left.IsPreservedBy F] [h₁.right.IsPreservedBy F]
    [h₂.left.IsPreservedBy F] [h₂.right.IsPreservedBy F] :
    F.map (ShortComplex.homologyMap' φ h₁ h₂) =
      ShortComplex.homologyMap' (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) :=
  LeftHomologyData.map_leftHomologyMap' _ _ _ _

noncomputable def mapCyclesIso [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).cycles ≅ F.obj S.cycles :=
  (S.leftHomologyData.map F).cyclesIso

noncomputable def mapLeftHomologyIso [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).leftHomology ≅ F.obj S.leftHomology :=
  (S.leftHomologyData.map F).leftHomologyIso

noncomputable def mapOpcyclesIso [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).opcycles ≅ F.obj S.opcycles :=
  (S.rightHomologyData.map F).opcyclesIso

noncomputable def mapRightHomologyIso [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).rightHomology ≅ F.obj S.rightHomology :=
  (S.rightHomologyData.map F).rightHomologyIso

noncomputable def mapHomologyIso [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homology ≅ F.obj S.homology :=
  (S.homologyData.left.map F).homologyIso

noncomputable def mapHomologyIso' [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesRightHomologyOf S] :
    (S.map F).homology ≅ F.obj S.homology :=
  (S.homologyData.right.map F).homologyIso ≪≫ F.mapIso S.homologyData.right.homologyIso.symm

variable {S}

lemma LeftHomologyData.mapCyclesIso_eq [S.HasHomology]
    [F.PreservesLeftHomologyOf S] :
    S.mapCyclesIso F = (hl.map F).cyclesIso ≪≫ F.mapIso hl.cyclesIso.symm := by
  ext
  dsimp [mapCyclesIso, cyclesIso]
  simp only [map_cyclesMap', ← cyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

lemma LeftHomologyData.mapLeftHomologyIso_eq [S.HasHomology]
    [F.PreservesLeftHomologyOf S] :
    S.mapLeftHomologyIso F = (hl.map F).leftHomologyIso ≪≫ F.mapIso hl.leftHomologyIso.symm := by
  ext
  dsimp [mapLeftHomologyIso, leftHomologyIso]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

lemma RightHomologyData.mapOpcyclesIso_eq [S.HasHomology]
    [F.PreservesRightHomologyOf S] :
    S.mapOpcyclesIso F = (hr.map F).opcyclesIso ≪≫ F.mapIso hr.opcyclesIso.symm := by
  ext
  dsimp [mapOpcyclesIso, opcyclesIso]
  simp only [map_opcyclesMap', ← opcyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

lemma RightHomologyData.mapRightHomologyIso_eq [S.HasHomology]
    [F.PreservesRightHomologyOf S] :
    S.mapRightHomologyIso F = (hr.map F).rightHomologyIso ≪≫
      F.mapIso hr.rightHomologyIso.symm := by
  ext
  dsimp [mapRightHomologyIso, rightHomologyIso]
  simp only [map_rightHomologyMap', ← rightHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

lemma LeftHomologyData.mapHomologyIso_eq [S.HasHomology]
    [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    S.mapHomologyIso F = (hl.map F).homologyIso ≪≫ F.mapIso hl.homologyIso.symm := by
  ext
  dsimp only [mapHomologyIso, homologyIso, ShortComplex.leftHomologyIso,
    leftHomologyMapIso', leftHomologyIso, Functor.mapIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [F.map_comp, map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id,
    Functor.map_id, Functor.mapShortComplex_obj]

lemma RightHomologyData.mapHomologyIso'_eq [S.HasHomology]
    [(S.map F).HasHomology] [F.PreservesRightHomologyOf S] :
    S.mapHomologyIso' F = (hr.map F).homologyIso ≪≫ F.mapIso hr.homologyIso.symm := by
  ext
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, mapHomologyIso', homologyIso,
    rightHomologyIso, rightHomologyMapIso', ShortComplex.rightHomologyIso]
  simp only [assoc, F.map_comp, map_rightHomologyMap', ← rightHomologyMap'_comp_assoc]

@[reassoc]
lemma mapCyclesIso_hom_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    cyclesMap (F.mapShortComplex.map φ) ≫ (S₂.mapCyclesIso F).hom =
      (S₁.mapCyclesIso F).hom ≫ F.map (cyclesMap φ) := by
  dsimp only [cyclesMap, mapCyclesIso, LeftHomologyData.cyclesIso, cyclesMapIso', Iso.refl]
  simp only [LeftHomologyData.map_cyclesMap', Functor.mapShortComplex_obj, ← cyclesMap'_comp,
    comp_id, id_comp]

@[reassoc]
lemma mapCyclesIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (cyclesMap φ) ≫ (S₂.mapCyclesIso F).inv =
      (S₁.mapCyclesIso F).inv ≫ cyclesMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapCyclesIso F).hom, ← mapCyclesIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

@[reassoc]
lemma mapLeftHomologyIso_hom_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    leftHomologyMap (F.mapShortComplex.map φ) ≫ (S₂.mapLeftHomologyIso F).hom =
      (S₁.mapLeftHomologyIso F).hom ≫ F.map (leftHomologyMap φ) := by
  dsimp only [leftHomologyMap, mapLeftHomologyIso, LeftHomologyData.leftHomologyIso,
    leftHomologyMapIso', Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', Functor.mapShortComplex_obj,
    ← leftHomologyMap'_comp, comp_id, id_comp]

@[reassoc]
lemma mapLeftHomologyIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (leftHomologyMap φ) ≫ (S₂.mapLeftHomologyIso F).inv =
      (S₁.mapLeftHomologyIso F).inv ≫ leftHomologyMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapLeftHomologyIso F).hom, ← mapLeftHomologyIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

@[reassoc]
lemma mapOpcyclesIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    opcyclesMap (F.mapShortComplex.map φ) ≫ (S₂.mapOpcyclesIso F).hom =
      (S₁.mapOpcyclesIso F).hom ≫ F.map (opcyclesMap φ) := by
  dsimp only [opcyclesMap, mapOpcyclesIso, RightHomologyData.opcyclesIso, opcyclesMapIso', Iso.refl]
  simp only [RightHomologyData.map_opcyclesMap', Functor.mapShortComplex_obj, ← opcyclesMap'_comp,
    comp_id, id_comp]

@[reassoc]
lemma mapOpcyclesIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (opcyclesMap φ) ≫ (S₂.mapOpcyclesIso F).inv =
      (S₁.mapOpcyclesIso F).inv ≫ opcyclesMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapOpcyclesIso F).hom, ← mapOpcyclesIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

@[reassoc]
lemma mapRightHomologyIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    rightHomologyMap (F.mapShortComplex.map φ) ≫ (S₂.mapRightHomologyIso F).hom =
      (S₁.mapRightHomologyIso F).hom ≫ F.map (rightHomologyMap φ) := by
  dsimp only [rightHomologyMap, mapRightHomologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', Iso.refl]
  simp only [RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    ← rightHomologyMap'_comp, comp_id, id_comp]

@[reassoc]
lemma mapRightHomologyIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (rightHomologyMap φ) ≫ (S₂.mapRightHomologyIso F).inv =
      (S₁.mapRightHomologyIso F).inv ≫ rightHomologyMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapRightHomologyIso F).hom, ← mapRightHomologyIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

@[reassoc]
lemma mapHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ ≫
      (S₂.mapHomologyIso F).hom = (S₁.mapHomologyIso F).hom ≫ F.map (homologyMap φ) := by
  dsimp only [homologyMap, homologyMap', mapHomologyIso, LeftHomologyData.homologyIso,
    LeftHomologyData.leftHomologyIso, leftHomologyMapIso', leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, id_comp]

@[reassoc]
lemma mapHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (homologyMap φ) ≫ (S₂.mapHomologyIso F).inv =
      (S₁.mapHomologyIso F).inv ≫
      @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ := by
  rw [← cancel_epi (S₁.mapHomologyIso F).hom, ← mapHomologyIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

@[reassoc]
lemma mapHomologyIso'_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ ≫
      (S₂.mapHomologyIso' F).hom = (S₁.mapHomologyIso' F).hom ≫ F.map (homologyMap φ) := by
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso, mapHomologyIso']
  simp only [← RightHomologyData.rightHomologyIso_hom_naturality_assoc _
    ((homologyData S₁).right.map F) ((homologyData S₂).right.map F), assoc,
    ← RightHomologyData.map_rightHomologyMap', ← F.map_comp,
    RightHomologyData.rightHomologyIso_inv_naturality _
      (homologyData S₁).right (homologyData S₂).right]

@[reassoc]
lemma mapHomologyIso'_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (homologyMap φ) ≫ (S₂.mapHomologyIso' F).inv = (S₁.mapHomologyIso' F).inv ≫
      @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ := by
  rw [← cancel_epi (S₁.mapHomologyIso' F).hom, ← mapHomologyIso'_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

variable (S)

lemma mapHomologyIso'_eq_mapHomologyIso [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    S.mapHomologyIso' F = S.mapHomologyIso F := by
  ext
  rw [S.homologyData.left.mapHomologyIso_eq F, S.homologyData.right.mapHomologyIso'_eq F]
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso, LeftHomologyData.homologyIso,
    leftHomologyIso, LeftHomologyData.leftHomologyIso]
  simp only [RightHomologyData.map_H, rightHomologyMapIso'_inv, rightHomologyMapIso'_hom, assoc,
    Functor.map_comp, RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    Functor.map_id, LeftHomologyData.map_H, leftHomologyMapIso'_inv, leftHomologyMapIso'_hom,
    LeftHomologyData.map_leftHomologyMap', ← rightHomologyMap'_comp_assoc, ← leftHomologyMap'_comp,
    ← leftHomologyMap'_comp_assoc, id_comp]
  have γ : HomologyMapData (𝟙 (S.map F)) (map S F).homologyData (S.homologyData.map F) := default
  have eq := γ.comm
  rw [← γ.left.leftHomologyMap'_eq, ← γ.right.rightHomologyMap'_eq] at eq
  dsimp at eq
  simp only [← reassoc_of% eq, ← F.map_comp, Iso.hom_inv_id, F.map_id, comp_id]

section

variable {F G S}
variable (h : LeftHomologyData S) (τ : F ⟶ G)
  [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S]
  [F.PreservesRightHomologyOf S] [G.PreservesRightHomologyOf S]

@[simps]
def leftHomologyMapDataOfNatTrans :
    LeftHomologyMapData (S.mapNatTrans τ) (h.map F) (h.map G) where
  φK := τ.app h.K
  φH := τ.app h.H

variable (S)

lemma homologyMap_mapNatTrans [S.HasHomology] :
    homologyMap (S.mapNatTrans τ) =
      (S.mapHomologyIso F).hom ≫ τ.app S.homology ≫ (S.mapHomologyIso G).inv :=
  (leftHomologyMapDataOfNatTrans S.homologyData.left τ).homologyMap_eq


end

section

variable [HasKernels C] [HasCokernels C]
  [HasKernels D] [HasCokernels D]

noncomputable def cyclesFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.cyclesFunctor D ≅
      ShortComplex.cyclesFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapCyclesIso F)
    (fun f => ShortComplex.mapCyclesIso_hom_naturality f F)

noncomputable def leftHomologyFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.leftHomologyFunctor D ≅
      ShortComplex.leftHomologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapLeftHomologyIso F)
    (fun f => ShortComplex.mapLeftHomologyIso_hom_naturality f F)

noncomputable def opcyclesFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.opcyclesFunctor D ≅
      ShortComplex.opcyclesFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapOpcyclesIso F)
    (fun f => ShortComplex.mapOpcyclesIso_hom_naturality f F)

noncomputable def rightHomologyFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.rightHomologyFunctor D ≅
      ShortComplex.rightHomologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapRightHomologyIso F)
    (fun f => ShortComplex.mapRightHomologyIso_hom_naturality f F)

end

noncomputable def homologyFunctorIso
    [CategoryWithHomology C] [CategoryWithHomology D] [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.homologyFunctor D ≅
      ShortComplex.homologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality f F)

section

variable {φ hl₁ hl₂ hr₁ hr₂}

lemma LeftHomologyMapData.quasiIso_map_iff
    [(F.mapShortComplex.obj S₁).HasHomology]
    [(F.mapShortComplex.obj S₂).HasHomology]
    [hl₁.IsPreservedBy F] [hl₂.IsPreservedBy F] :
    QuasiIso (F.mapShortComplex.map φ) ↔ IsIso (F.map ψl.φH) :=
  (ψl.map F).quasiIso_iff

lemma RightHomologyMapData.quasiIso_map_iff
    [(F.mapShortComplex.obj S₁).HasHomology]
    [(F.mapShortComplex.obj S₂).HasHomology]
    [hr₁.IsPreservedBy F] [hr₂.IsPreservedBy F] :
    QuasiIso (F.mapShortComplex.map φ) ↔ IsIso (F.map ψr.φH) :=
  (ψr.map F).quasiIso_iff

variable (φ) [S₁.HasHomology] [S₂.HasHomology]
    [(F.mapShortComplex.obj S₁).HasHomology] [(F.mapShortComplex.obj S₂).HasHomology]

instance quasiIso_map_of_preservesLeftHomology
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂]
    [QuasiIso φ] : QuasiIso (F.mapShortComplex.map φ) := by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff, LeftHomologyMapData.map_φH]
  infer_instance

instance quasiIso_map_of_preservesRightHomology
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂]
    [QuasiIso φ] : QuasiIso (F.mapShortComplex.map φ) := by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff, RightHomologyMapData.map_φH]
  infer_instance

lemma quasiIso_map_iff_of_preservesRightHomology
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂]
    [ReflectsIsomorphisms F] :
    QuasiIso (F.mapShortComplex.map φ) ↔ QuasiIso φ := by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  rw [γ.quasiIso_iff, (γ.map F).quasiIso_iff, RightHomologyMapData.map_φH]
  constructor
  . intro
    exact isIso_of_reflects_iso _ F
  . intro
    infer_instance

end

end ShortComplex

namespace Functor

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  (S : ShortComplex C)

noncomputable def preservesLeftHomologyOf_of_zero_left (hf : S.f = 0)
    [PreservesLimit (parallelPair S.g 0) F] :
    F.PreservesLeftHomologyOf S := ⟨fun h =>
  { g := by infer_instance
    f' := Limits.preservesCokernelZero' _ _
      (by rw [← cancel_mono h.i, h.f'_i, zero_comp, hf]) }⟩

noncomputable def preservesRightHomologyOf_of_zero_right (hg : S.g = 0)
    [PreservesColimit (parallelPair S.f 0) F] :
    F.PreservesRightHomologyOf S := ⟨fun h =>
  { f := by infer_instance
    g' := Limits.preservesKernelZero' _ _
      (by rw [← cancel_epi h.p, h.p_g', comp_zero, hg]) }⟩

noncomputable def preservesLeftHomologyOf_of_zero_right (hg : S.g = 0)
    [PreservesColimit (parallelPair S.f 0) F] :
    F.PreservesLeftHomologyOf S := ⟨fun h =>
  { g := by
      rw [hg]
      infer_instance
    f' := by
      have := h.isIso_i hg
      let e : parallelPair h.f' 0 ≅ parallelPair S.f 0 :=
        parallelPair.ext (Iso.refl _) (asIso h.i) (by aesop_cat) (by aesop_cat)
      exact Limits.preservesColimitOfIsoDiagram F e.symm}⟩

noncomputable def preservesRightHomologyOf_of_zero_left (hf : S.f = 0)
    [PreservesLimit (parallelPair S.g 0) F] :
    F.PreservesRightHomologyOf S := ⟨fun h =>
  { f := by
      rw [hf]
      infer_instance
    g' := by
      have := h.isIso_p hf
      let e : parallelPair S.g 0 ≅ parallelPair h.g' 0 :=
        parallelPair.ext (asIso h.p) (Iso.refl _) (by aesop_cat) (by aesop_cat)
      exact Limits.preservesLimitOfIsoDiagram F e }⟩

end Functor

lemma NatTrans.app_homology {F G : C ⥤ D} [HasZeroMorphisms C] [HasZeroMorphisms D] (τ : F ⟶ G)
    (S : ShortComplex C) [S.HasHomology] [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S]
    [G.PreservesRightHomologyOf S] :
    τ.app S.homology = (S.mapHomologyIso F).inv ≫
      ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom := by
  rw [ShortComplex.homologyMap_mapNatTrans, assoc, assoc, Iso.inv_hom_id,
    comp_id, Iso.inv_hom_id_assoc]

end CategoryTheory
