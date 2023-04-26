import Mathlib.Algebra.Homology.ShortComplex.Homology

namespace CategoryTheory

open Category Limits ZeroObject

variable {C D : Type _} [Category C] [Category D]


namespace Limits

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {X Y : C} {f : X ⟶ Y}  (c : KernelFork f) (c' : CokernelCofork f)
  (hc : IsLimit c) (hc' : IsColimit c') (F : C ⥤ D) [F.PreservesZeroMorphisms]

@[reassoc (attr := simp)]
lemma KernelFork.map_condition : F.map c.ι ≫ F.map f = 0 := by
  rw [← F.map_comp, c.condition, F.map_zero]

def KernelFork.map : KernelFork (F.map f) :=
  KernelFork.ofι (F.map c.ι) (c.map_condition F)

@[simp]
lemma KernelFork.map_ι : (c.map F).ι = F.map c.ι := rfl

@[reassoc (attr := simp)]
lemma CokernelCofork.map_condition : F.map f ≫ F.map c'.π = 0 := by
  rw [← F.map_comp, c'.condition, F.map_zero]

def CokernelCofork.map : CokernelCofork (F.map f) :=
  CokernelCofork.ofπ (F.map c'.π) (c'.map_condition F)

@[simp]
lemma CokernelCofork.map_π : (c'.map F).π = F.map c'.π := rfl

def KernelFork.mapIsLimit [PreservesLimit (parallelPair f 0) F] :
    IsLimit (c.map F) := by
  let e : parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  refine' IsLimit.postcomposeInvEquiv e (c.map F)
    (IsLimit.ofIsoLimit (isLimitOfPreserves F hc) _)
  exact Cones.ext (Iso.refl _) (by rintro (_|_) <;> aesop_cat)

def CokernelCofork.mapIsColimit [PreservesColimit (parallelPair f 0) F] :
    IsColimit (c'.map F) := by
  let e : parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  refine' IsColimit.precomposeHomEquiv e (c'.map F)
    (IsColimit.ofIsoColimit (isColimitOfPreserves F hc') _)
  exact Cocones.ext (Iso.refl _) (by rintro (_|_) <;> aesop_cat)

end Limits


namespace Functor

variable (F : C ⥤ D)

class PreservesHomology (F : C ⥤ D) [HasZeroMorphisms C] [HasZeroMorphisms D]
  [PreservesZeroMorphisms F] where
  preserves_kernels : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F
  preserves_cokernels : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F

lemma PreservesHomology.preserves_kernel (F : C ⥤ D) [HasZeroMorphisms C] [HasZeroMorphisms D]
    [PreservesZeroMorphisms F] [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) F :=
  PreservesHomology.preserves_kernels _

lemma PreservesHomology.preserves_cokernel (F : C ⥤ D) [HasZeroMorphisms C] [HasZeroMorphisms D]
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

lemma IsPreservedBy.hg (h : S.LeftHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.IsPreservedBy F] : PreservesLimit (parallelPair S.g 0) F :=
  @IsPreservedBy.g _ _ _ _ _ _ _ h F _ _

lemma IsPreservedBy.hf' (h : S.LeftHomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
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

def map_f' : (h.map F).f' = F.map h.f' := by
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

end ShortComplex

end CategoryTheory

#exit

import algebra.homology.short_complex.homology

noncomputable theory


namespace category_theory

open category
open_locale zero_object

variables {C D : Type*} [category C] [category D]

namespace limits

@[simps]
def parallel_pair.comp_nat_iso'
  {C D : Type*} [category C] [category D] (F : C ⥤ D) [has_zero_morphisms C] [has_zero_morphisms D]
  [F.preserves_zero_morphisms] {X Y : C} (f : X ⟶ Y) (f' : F.obj X ⟶ F.obj Y)
  (h : f' = F.map f) :
  parallel_pair f 0 ⋙ F ≅ parallel_pair f' 0 :=
parallel_pair.ext (iso.refl _) (iso.refl _) (by tidy) (by tidy)

@[simps]
def parallel_pair.comp_nat_iso
  {C D : Type*} [category C] [category D] (F : C ⥤ D) [has_zero_morphisms C] [has_zero_morphisms D]
  [F.preserves_zero_morphisms] {X Y : C} (f : X ⟶ Y) :
  parallel_pair f 0 ⋙ F ≅ parallel_pair (F.map f) 0 :=
category_theory.limits.parallel_pair.comp_nat_iso' F f _ rfl

@[simps]
def kernel_fork.map {X Y : C} {f : X ⟶ Y} [has_zero_morphisms C] [has_zero_morphisms D]
  (c : kernel_fork f) (F : C ⥤ D) [F.preserves_zero_morphisms] :
  kernel_fork (F.map f) :=
kernel_fork.of_ι (F.map c.ι) (by rw [← F.map_comp, c.condition, F.map_zero])

def kernel_fork.map_is_limit {X Y : C} {f : X ⟶ Y} [has_zero_morphisms C] [has_zero_morphisms D]
  {c : kernel_fork f} (hc : is_limit c) (F : C ⥤ D) [F.preserves_zero_morphisms]
  [preserves_limit (parallel_pair f 0) F] :
  is_limit (c.map F) :=
begin
  equiv_rw (is_limit.postcompose_inv_equiv (parallel_pair.comp_nat_iso F f) _).symm,
  refine is_limit.of_iso_limit (is_limit_of_preserves F hc) _,
  refine cones.ext (iso.refl _) _,
  rintro (_|_),
  { tidy, },
  { dsimp,
    simp only [kernel_fork.app_one, category.comp_id, category.id_comp,
      ← F.map_comp, c.condition], },
end

instance preserves_kernel_zero {X Y : C} [has_zero_morphisms C] [has_zero_morphisms D] (F : C ⥤ D)
  [F.preserves_zero_morphisms] :
  preserves_limit (parallel_pair (0 : X ⟶ Y) 0) F :=
⟨λ c hc, begin
  haveI := kernel_fork.is_limit.is_iso_ι_of_zero c hc rfl,
  equiv_rw (is_limit.postcompose_inv_equiv (parallel_pair.comp_nat_iso F _).symm _).symm,
  refine is_limit.of_iso_limit (kernel_zero _ (F.map_zero _ _)) _,
  symmetry,
  exact (fork.ext (F.map_iso (as_iso (fork.ι c))) rfl),
end⟩

instance preserves_cokernel_zero {X Y : C} [has_zero_morphisms C] [has_zero_morphisms D] (F : C ⥤ D)
  [F.preserves_zero_morphisms] :
  preserves_colimit (parallel_pair (0 : X ⟶ Y) 0) F :=
⟨λ c hc, begin
  haveI := cokernel_cofork.is_colimit.is_iso_π_of_zero c hc rfl,
  equiv_rw (is_colimit.precompose_hom_equiv (parallel_pair.comp_nat_iso F _).symm _).symm,
  exact is_colimit.of_iso_colimit (cokernel_zero _ (F.map_zero _ _))
    (cofork.ext (F.map_iso (as_iso (cofork.π c))) rfl),
end⟩

end limits

open limits

namespace short_complex

variables [has_zero_morphisms C] [has_zero_morphisms D]
  {S S₁ S₂ : short_complex C}

namespace right_homology_data

class is_preserved_by (h : S.right_homology_data)
  (F : C ⥤ D) [F.preserves_zero_morphisms] :=
(hf [] : preserves_colimit (parallel_pair S.f 0) F)
(hg' [] : preserves_limit (parallel_pair h.g' 0) F)

@[priority 100]
instance is_preserved_by_of_preserves_homology (h : S.right_homology_data) (F : C ⥤ D)
  [F.preserves_zero_morphisms] [F.preserves_homology] : h.is_preserved_by F :=
{ hg' := category_theory.functor.preserves_homology.preserves_kernels F _,
  hf := category_theory.functor.preserves_homology.preserves_cokernels F _, }

@[simps]
def map (h : S.right_homology_data) (F : C ⥤ D) [F.preserves_zero_morphisms]
  [h.is_preserved_by F] :
  (S.map F).right_homology_data :=
begin
  haveI := is_preserved_by.hf h F,
  haveI := is_preserved_by.hg' h F,
  have wp : F.map S.f ≫ F.map h.p = 0 := by rw [← F.map_comp, h.wp, F.map_zero],
  have hp : is_colimit (cokernel_cofork.of_π (F.map h.p) wp),
  { equiv_rw (is_colimit.precompose_hom_equiv
    (category_theory.limits.parallel_pair.comp_nat_iso F S.f) _).symm,
    refine is_colimit.of_iso_colimit (is_colimit_of_preserves F h.hp)
      (cocones.ext (iso.refl _) _),
    rintro (_|_),
    { tidy, },
    { dsimp,
      simp only [comp_id, id_comp, F.map_comp], }, },
  let g' : F.obj h.Q ⟶ F.obj S.X₃ := hp.desc (cokernel_cofork.of_π (S.map F).g (S.map F).zero),
  have hg' : g' = F.map h.g',
  { apply cofork.is_colimit.hom_ext hp,
    erw cofork.is_colimit.π_desc hp,
    simp only [cokernel_cofork.π_of_π, map_g, ← F.map_comp, h.p_g'], },
  have wι : F.map h.ι ≫ g' = 0,
  { rw [hg', ← F.map_comp, h.ι_g', F.map_zero], },
  have hι : is_limit (kernel_fork.of_ι (F.map h.ι) wι),
  { equiv_rw (is_limit.postcompose_inv_equiv
      (category_theory.limits.parallel_pair.comp_nat_iso' F h.g' _ hg') _).symm,
    refine is_limit.of_iso_limit (is_limit_of_preserves F h.hι)
      (cones.ext (iso.refl _) _),
    rintro (_|_),
    { tidy, },
    { dsimp,
      simp only [id_comp, comp_id, F.map_comp],
      erw hg',
      refl, }, },
  exact
  { Q := F.obj h.Q,
    H := F.obj h.H,
    p := F.map h.p,
    ι := F.map h.ι,
    wp := wp,
    hp := hp,
    wι := wι,
    hι := hι, },
end

@[simp] lemma map_g' (h : S.right_homology_data) (F : C ⥤ D) [F.preserves_zero_morphisms]
  [h.is_preserved_by F] : (h.map F).g' = F.map h.g' :=
by rw [← cancel_epi (h.map F).p, p_g', map_g, map_p, ← F.map_comp, p_g']

end right_homology_data

@[simps]
def right_homology_map_data.map {φ : S₁ ⟶ S₂} {h₁ : S₁.right_homology_data}
  {h₂ : S₂.right_homology_data} (ψ : right_homology_map_data φ h₁ h₂) (F : C ⥤ D)
  [F.preserves_zero_morphisms] [h₁.is_preserved_by F] [h₂.is_preserved_by F] :
  right_homology_map_data (F.map_short_complex.map φ) (h₁.map F) (h₂.map F) :=
{ φQ := F.map ψ.φQ,
  φH := F.map ψ.φH,
  commp' := by simpa only [F.map_comp] using F.congr_map ψ.commp,
  commg'' := by simpa only [right_homology_data.map_g', F.map_comp] using F.congr_map ψ.commg',
  commι' := by simpa only [F.map_comp] using F.congr_map ψ.commι, }

namespace homology_data

@[simp]
def map (h : S.homology_data) (F : C ⥤ D) [F.preserves_zero_morphisms]
  [h.left.is_preserved_by F] [h.right.is_preserved_by F] :
  (S.map F).homology_data :=
begin
  haveI := left_homology_data.is_preserved_by h.left F,
  haveI := right_homology_data.is_preserved_by h.right F,
  exact
  { left := h.left.map F,
    right := h.right.map F,
    iso := F.map_iso h.iso,
    comm := by simpa only [F.map_comp] using F.congr_map h.comm, },
end

end homology_data

@[simps]
def homology_map_data.map {φ : S₁ ⟶ S₂} {h₁ : S₁.homology_data}
  {h₂ : S₂.homology_data} (ψ : homology_map_data φ h₁ h₂) (F : C ⥤ D)
  [F.preserves_zero_morphisms] [h₁.left.is_preserved_by F] [h₁.right.is_preserved_by F]
  [h₂.left.is_preserved_by F] [h₂.right.is_preserved_by F] :
  homology_map_data (F.map_short_complex.map φ) (h₁.map F) (h₂.map F) :=
{ left := ψ.left.map F,
  right := ψ.right.map F, }

end short_complex

open limits short_complex

namespace functor

variables (F : C ⥤ D) [has_zero_morphisms C] [has_zero_morphisms D]
  [preserves_zero_morphisms F] (S : short_complex C) {S₁ S₂ : short_complex C}

class preserves_left_homology_of :=
(condition' [] : ∀ (h : S.left_homology_data), h.is_preserved_by F)

class preserves_right_homology_of :=
(condition' [] : ∀ (h : S.right_homology_data), h.is_preserved_by F)

@[priority 100]
instance preserves_left_homology_of.condition (h : S.left_homology_data)
  [F.preserves_left_homology_of S] :
  h.is_preserved_by F := preserves_left_homology_of.condition' F h

@[priority 100]
instance preserves_right_homology_of.condition (h : S.right_homology_data)
  [F.preserves_right_homology_of S] :
  h.is_preserved_by F := preserves_right_homology_of.condition' F h

instance has_left_homology_of_preserves_left_homology_of
  [S.has_left_homology] [F.preserves_left_homology_of S] : (S.map F).has_left_homology :=
begin
  haveI := preserves_left_homology_of.condition F S,
  exact has_left_homology.mk' (S.some_left_homology_data.map F)
end

instance has_left_homology_of_preserves_left_homology_of'
  [S.has_left_homology] [F.preserves_left_homology_of S] :
  (F.map_short_complex.obj S).has_left_homology :=
by { change (S.map F).has_left_homology, apply_instance, }

instance has_right_homology_of_preserves_right_homology_of
  [S.has_right_homology] [F.preserves_right_homology_of S] : (S.map F).has_right_homology :=
begin
  haveI := preserves_right_homology_of.condition F S,
  exact has_right_homology.mk' (S.some_right_homology_data.map F)
end

instance has_right_homology_of_preserves_right_homology_of'
  [S.has_right_homology] [F.preserves_right_homology_of S] :
  (F.map_short_complex.obj S).has_right_homology :=
by { change (S.map F).has_right_homology, apply_instance, }

instance has_homology_of_preserves_left_and_right_homology_of
  [S.has_homology] [F.preserves_left_homology_of S]
  [F.preserves_right_homology_of S] : (S.map F).has_homology :=
begin
  haveI := preserves_right_homology_of.condition F S,
  haveI := preserves_left_homology_of.condition F S,
  exact has_homology.mk' (S.some_homology_data.map F)
end

instance has_homology_of_preserves_left_and_right_homology_of'
  [S.has_homology] [F.preserves_left_homology_of S]
  [F.preserves_right_homology_of S] : (F.map_short_complex.obj S).has_homology :=
begin
  change (S.map F).has_homology,
  apply_instance,
end

@[priority 100]
instance preserves_left_homology_of_of_preserves_homology
  [F.preserves_homology] (S : short_complex C) :
    F.preserves_left_homology_of S :=
⟨λ h, infer_instance⟩

@[priority 100]
instance preserves_right_homology_of_of_preserves_homology
  [F.preserves_homology] (S : short_complex C) :
    F.preserves_right_homology_of S :=
⟨λ h, infer_instance⟩

def left_homology_iso [S.has_left_homology] [F.preserves_left_homology_of S] :
  (S.map F).left_homology ≅ F.obj S.left_homology :=
begin
  haveI := preserves_left_homology_of.condition F S,
  exact (S.some_left_homology_data.map F).left_homology_iso,
end

def right_homology_iso [S.has_right_homology] [F.preserves_right_homology_of S] :
  (S.map F).right_homology ≅ F.obj S.right_homology :=
begin
  haveI := preserves_right_homology_of.condition F S,
  exact (S.some_right_homology_data.map F).right_homology_iso,
end

def homology_iso [S.has_homology] [F.preserves_left_homology_of S]
  [F.preserves_right_homology_of S] :
  (S.map F).homology ≅ F.obj S.homology :=
begin
  haveI := preserves_left_homology_of.condition F S,
  haveI := preserves_right_homology_of.condition F S,
  exact (S.some_homology_data.map F).homology_iso,
end

lemma map_left_homology_map' (F : C ⥤ D) (φ : S₁ ⟶ S₂)
  (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data)
  [F.preserves_zero_morphisms] [h₁.is_preserved_by F] [h₂.is_preserved_by F] :
  F.map (left_homology_map' φ h₁ h₂) =
    left_homology_map' (F.map_short_complex.map φ) (h₁.map F) (h₂.map F) :=
begin
  let ψ := left_homology_map_data.some φ h₁ h₂,
  rw [ψ.left_homology_map'_eq, (ψ.map F).left_homology_map'_eq,
    left_homology_map_data.map_φH],
end

lemma left_homology_iso_naturality
  [S₁.has_left_homology] [F.preserves_left_homology_of S₁]
  [S₂.has_left_homology] [F.preserves_left_homology_of S₂] (f : S₁ ⟶ S₂) :
  left_homology_map (F.map_short_complex.map f) ≫ (F.left_homology_iso S₂).hom =
    (F.left_homology_iso S₁).hom ≫ F.map (left_homology_map f) :=
begin
  letI := preserves_left_homology_of.condition F S₁,
  letI := preserves_left_homology_of.condition F S₂,
  dsimp only [left_homology_map, left_homology_iso, left_homology_data.left_homology_iso,
    left_homology_map_iso', iso.refl, map_short_complex_obj],
  rw [F.map_left_homology_map', ← left_homology_map'_comp,
    ← left_homology_map'_comp, comp_id, id_comp],
end

lemma map_right_homology_map' (F : C ⥤ D) (φ : S₁ ⟶ S₂)
  (h₁ : S₁.right_homology_data) (h₂ : S₂.right_homology_data)
  [F.preserves_zero_morphisms] [h₁.is_preserved_by F] [h₂.is_preserved_by F] :
  F.map (right_homology_map' φ h₁ h₂) =
    right_homology_map' (F.map_short_complex.map φ) (h₁.map F) (h₂.map F) :=
begin
  let ψ := right_homology_map_data.some φ h₁ h₂,
  rw [ψ.right_homology_map'_eq, (ψ.map F).right_homology_map'_eq,
    right_homology_map_data.map_φH],
end

lemma right_homology_iso_naturality
  [S₁.has_right_homology] [F.preserves_right_homology_of S₁]
  [S₂.has_right_homology] [F.preserves_right_homology_of S₂] (f : S₁ ⟶ S₂) :
  right_homology_map (F.map_short_complex.map f) ≫ (F.right_homology_iso S₂).hom =
    (F.right_homology_iso S₁).hom ≫ F.map (right_homology_map f) :=
begin
  letI := preserves_right_homology_of.condition F S₁,
  letI := preserves_right_homology_of.condition F S₂,
  dsimp only [right_homology_map, right_homology_iso, right_homology_data.right_homology_iso,
    right_homology_map_iso', iso.refl, map_short_complex_obj],
  rw [F.map_right_homology_map', ← right_homology_map'_comp,
    ← right_homology_map'_comp, comp_id, id_comp],
end

lemma map_homology_map' (F : C ⥤ D) (φ : S₁ ⟶ S₂)
  (h₁ : S₁.homology_data) (h₂ : S₂.homology_data)
  [F.preserves_zero_morphisms] [h₁.left.is_preserved_by F] [h₁.right.is_preserved_by F]
  [h₂.left.is_preserved_by F] [h₂.right.is_preserved_by F] :
  F.map (homology_map' φ h₁ h₂) =
    homology_map' (F.map_short_complex.map φ) (h₁.map F) (h₂.map F) :=
map_left_homology_map' _ _ _ _

lemma homology_iso_naturality
  [S₁.has_homology] [F.preserves_left_homology_of S₁] [F.preserves_right_homology_of S₁]
  [S₂.has_homology] [F.preserves_left_homology_of S₂] [F.preserves_right_homology_of S₂]
  (f : S₁ ⟶ S₂) :
  homology_map (F.map_short_complex.map f) ≫ (F.homology_iso S₂).hom =
    (F.homology_iso S₁).hom ≫ F.map (homology_map f) :=
begin
  letI := preserves_left_homology_of.condition F S₁,
  letI := preserves_left_homology_of.condition F S₂,
  letI := preserves_right_homology_of.condition F S₁,
  letI := preserves_right_homology_of.condition F S₂,
  dsimp only [homology_map, homology_iso, homology_data.homology_iso,
    homology_map_iso', iso.refl, map_short_complex_obj],
  rw [F.map_homology_map', ← homology_map'_comp, ← homology_map'_comp, comp_id, id_comp],
end

@[simps]
def left_homology_nat_iso [category_with_left_homology C] [category_with_left_homology D]
  [F.preserves_homology] :
  F.map_short_complex ⋙ left_homology_functor D ≅ left_homology_functor C ⋙ F :=
nat_iso.of_components (λ S, left_homology_iso F S)
  (λ S₁ S₂ f, left_homology_iso_naturality F f)

@[simps]
def right_homology_nat_iso [category_with_right_homology C] [category_with_right_homology D]
  [F.preserves_homology] :
  F.map_short_complex ⋙ right_homology_functor D ≅ right_homology_functor C ⋙ F :=
nat_iso.of_components (λ S, right_homology_iso F S)
  (λ S₁ S₂ f, right_homology_iso_naturality F f)

@[simps]
def homology_nat_iso [category_with_homology C] [category_with_homology D]
  [F.preserves_homology] :
  F.map_short_complex ⋙ homology_functor D ≅ homology_functor C ⋙ F :=
nat_iso.of_components (λ S, homology_iso F S)
  (λ S₁ S₂ f, homology_iso_naturality F f)

end functor

namespace short_complex

variables [has_zero_morphisms C] [has_zero_morphisms D] {S₁ S₂ : short_complex C}

namespace left_homology_map_data

lemma quasi_iso_map_iff {φ : S₁ ⟶ S₂} {h₁ : left_homology_data S₁} {h₂ : left_homology_data S₂}
  (ψ : left_homology_map_data φ h₁ h₂) (F : C ⥤ D) [F.preserves_zero_morphisms]
  [(F.map_short_complex.obj S₁).has_homology]
  [(F.map_short_complex.obj S₂).has_homology]
  [h₁.is_preserved_by F] [h₂.is_preserved_by F] :
  short_complex.quasi_iso (F.map_short_complex.map φ) ↔ is_iso (F.map ψ.φH) :=
(ψ.map F).quasi_iso_iff

end left_homology_map_data

namespace right_homology_map_data

lemma quasi_iso_map_iff {φ : S₁ ⟶ S₂} {h₁ : right_homology_data S₁} {h₂ : right_homology_data S₂}
  (ψ : right_homology_map_data φ h₁ h₂) (F : C ⥤ D) [F.preserves_zero_morphisms]
  [(F.map_short_complex.obj S₁).has_homology]
  [(F.map_short_complex.obj S₂).has_homology]
  [h₁.is_preserved_by F] [h₂.is_preserved_by F] :
  short_complex.quasi_iso (F.map_short_complex.map φ) ↔ is_iso (F.map ψ.φH) :=
(ψ.map F).quasi_iso_iff

end right_homology_map_data

lemma quasi_iso_map_of_preserves_left_homology {φ : S₁ ⟶ S₂}
  [S₁.has_homology] [S₂.has_homology] (h : short_complex.quasi_iso φ)
  (F : C ⥤ D) [F.preserves_zero_morphisms] [F.preserves_left_homology_of S₁]
  [F.preserves_left_homology_of S₂]
  [(F.map_short_complex.obj S₁).has_homology]
  [(F.map_short_complex.obj S₂).has_homology] :
  short_complex.quasi_iso (F.map_short_complex.map φ) :=
begin
  haveI := functor.preserves_left_homology_of.condition F S₁,
  haveI := functor.preserves_left_homology_of.condition F S₂,
  let ψ := left_homology_map_data.some φ S₁.some_left_homology_data
    S₂.some_left_homology_data,
  haveI : is_iso ψ.φH := by simpa only [← ψ.quasi_iso_iff] using h,
  rw ψ.quasi_iso_map_iff F,
  apply_instance,
end

lemma quasi_iso_map_iff_of_preserves_left_homology (φ : S₁ ⟶ S₂)
  [S₁.has_homology] [S₂.has_homology]
  (F : C ⥤ D) [F.preserves_zero_morphisms] [F.preserves_left_homology_of S₁]
  [F.preserves_left_homology_of S₂]
  [(F.map_short_complex.obj S₁).has_homology]
  [(F.map_short_complex.obj S₂).has_homology] [reflects_isomorphisms F]:
  short_complex.quasi_iso (F.map_short_complex.map φ) ↔
    short_complex.quasi_iso φ :=
begin
  haveI := functor.preserves_left_homology_of.condition F S₁,
  haveI := functor.preserves_left_homology_of.condition F S₂,
  let ψ := left_homology_map_data.some φ S₁.some_left_homology_data
    S₂.some_left_homology_data,
  rw [ψ.quasi_iso_map_iff F, ψ.quasi_iso_iff],
  split,
  { introI,
    exact is_iso_of_reflects_iso ψ.φH F, },
  { introI,
    apply_instance, },
end

section

variables (F : C ⥤ D) [functor.preserves_zero_morphisms F] (S : short_complex C)

def preserves_left_homology_of_zero_left (hf : S.f = 0)
  [preserves_limit (parallel_pair S.g 0) F] :
  F.preserves_left_homology_of S :=
⟨λ h, begin
  split,
  { apply_instance, },
  { rw [show h.f' = 0, by rw [← cancel_mono h.i, h.f'_i, zero_comp, hf]],
    apply_instance, },
end⟩

def preserves_right_homology_of_zero_left (hf : S.f = 0)
  [preserves_limit (parallel_pair S.g 0) F] :
  F.preserves_right_homology_of S :=
⟨λ h, begin
  split,
  { rw hf, apply_instance, },
  { let e : parallel_pair S.g 0 ≅ parallel_pair h.g' 0,
    { haveI : is_iso h.p := h.is_iso_p_of_zero_f hf,
      exact parallel_pair.ext (as_iso h.p) (iso.refl _) (by tidy) (by tidy), },
    exact limits.preserves_limit_of_iso_diagram F e, },
end⟩

def preserves_left_homology_of_zero_right (hg : S.g = 0)
  [preserves_colimit (parallel_pair S.f 0) F] :
  F.preserves_left_homology_of S :=
⟨λ h, begin
  split,
  { rw hg, apply_instance, },
  { let e : parallel_pair h.f' 0 ≅ parallel_pair S.f 0,
    { haveI : is_iso h.i := h.is_iso_i_of_zero_g hg,
      refine parallel_pair.ext (iso.refl _) (as_iso h.i) (by tidy) (by tidy), },
    exact limits.preserves_colimit_of_iso_diagram F e.symm, },
end⟩

def preserves_right_homology_of_zero_right (hg : S.g = 0)
  [preserves_colimit (parallel_pair S.f 0) F] :
  F.preserves_right_homology_of S :=
⟨λ h, begin
  split,
  { apply_instance, },
  { rw [show h.g' = 0, by rw [← cancel_epi h.p, h.p_g', comp_zero, hg]],
    apply_instance, },
end⟩

end

end short_complex

end category_theory
