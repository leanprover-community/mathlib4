import Mathlib.Algebra.Homology.ShortComplex.Exact

namespace CategoryTheory

open Limits

variable (C : Type _) [Category C]

structure ShortComplex₄ [HasZeroMorphisms C] where
  {X₁ X₂ X₃ X₄ : C}
  f : X₁ ⟶ X₂
  g : X₂ ⟶ X₃
  h : X₃ ⟶ X₄
  zero₁ : f ≫ g = 0
  zero₂ : g ≫ h = 0

namespace ShortComplex₄

attribute [reassoc (attr := simp)] zero₁ zero₂

section

variable {C}
variable [HasZeroMorphisms C]

@[ext]
structure Hom (S₁ S₂ : ShortComplex₄ C) where
  τ₁ : S₁.X₁ ⟶ S₂.X₁
  τ₂ : S₁.X₂ ⟶ S₂.X₂
  τ₃ : S₁.X₃ ⟶ S₂.X₃
  τ₄ : S₁.X₄ ⟶ S₂.X₄
  commf : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ := by aesop_cat
  commg : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ := by aesop_cat
  commh : τ₃ ≫ S₂.h = S₁.h ≫ τ₄ := by aesop_cat

attribute [reassoc] Hom.commf Hom.commg Hom.commh
attribute [local simp] Hom.commf Hom.commg Hom.commh
  Hom.commf_assoc Hom.commg_assoc Hom.commh_assoc

variable (S : ShortComplex₄ C) {S₁ S₂ S₃ : ShortComplex₄ C}

/-- The identity morphism of a short complex. -/
@[simps]
def Hom.id : Hom S S where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
def Hom.comp (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃) : Hom S₁ S₃ where
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃
  τ₄ := φ₁₂.τ₄ ≫ φ₂₃.τ₄

instance : Category (ShortComplex₄ C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃)
    (h₄ : f.τ₄ = g.τ₄) : f = g :=
  Hom.ext _ _ h₁ h₂ h₃ h₄

/-- A constructor for morphisms in `ShortComplex₄ C` when the commutativity conditions
are not obvious. -/
@[simps]
def homMk {S₁ S₂ : ShortComplex₄ C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
    (τ₃ : S₁.X₃ ⟶ S₂.X₃) (τ₄ : S₁.X₄ ⟶ S₂.X₄) (commf : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
    (commg : τ₂ ≫ S₂.g = S₁.g ≫ τ₃) (commh : τ₃ ≫ S₂.h = S₁.h ≫ τ₄) :
  S₁ ⟶ S₂ := ⟨τ₁, τ₂, τ₃, τ₄, commf, commg, commh⟩

@[simp] lemma id_τ₁ : Hom.τ₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ : Hom.τ₂ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ : Hom.τ₃ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₄ : Hom.τ₄ (𝟙 S) = 𝟙 _ := rfl
@[reassoc] lemma comp_τ₁ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁ := rfl
@[reassoc] lemma comp_τ₂ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂ := rfl
@[reassoc] lemma comp_τ₃ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₃ = φ₁₂.τ₃ ≫ φ₂₃.τ₃ := rfl
@[reassoc] lemma comp_τ₄ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₄ = φ₁₂.τ₄ ≫ φ₂₃.τ₄ := rfl

attribute [simp] comp_τ₁ comp_τ₂ comp_τ₃ comp_τ₄

instance : Zero (S₁ ⟶ S₂) := ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0, τ₄ := 0 }⟩

variable (S₁ S₂)

@[simp] lemma zero_τ₁ : Hom.τ₁ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₂ : Hom.τ₂ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₃ : Hom.τ₃ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₄ : Hom.τ₄ (0 : S₁ ⟶ S₂) = 0 := rfl

variable {S₁ S₂}

instance : HasZeroMorphisms (ShortComplex C) where

@[simps]
def shortComplex₁ : ShortComplex C :=
  ShortComplex.mk _ _ S.zero₁

@[simps]
def shortComplex₂ : ShortComplex C :=
  ShortComplex.mk _ _ S.zero₂

structure Exact : Prop where
  exact₁ : S.shortComplex₁.Exact
  exact₂ : S.shortComplex₂.Exact

section

variable (hS : S.Exact) (cc : CokernelCofork S.f) (kf : KernelFork S.h)
  (hcc : IsColimit cc) (hkf : IsLimit kf)

def cokerToKer' : cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.f ≫ IsLimit.lift hkf (KernelFork.ofι _ S.zero₂) = 0 from
      Fork.IsLimit.hom_ext hkf (by simp)))

@[reassoc (attr := simp)]
lemma cokerToKer'_fac : cc.π ≫ S.cokerToKer' cc kf hcc hkf ≫ kf.ι = S.g := by
  simp [cokerToKer']

noncomputable def cokerToKer [HasCokernel S.f] [HasKernel S.h] : cokernel S.f ⟶ kernel S.h :=
  S.cokerToKer' (CokernelCofork.ofπ  _ (cokernel.condition S.f))
    (KernelFork.ofι _ (kernel.condition S.h)) (cokernelIsCokernel S.f) (kernelIsKernel S.h)

@[reassoc (attr := simp)]
lemma cokerToKer_fac [HasCokernel S.f] [HasKernel S.h] :
    cokernel.π S.f ≫ S.cokerToKer ≫ kernel.ι S.h = S.g :=
  S.cokerToKer'_fac _ _ (cokernelIsCokernel S.f) (kernelIsKernel S.h)

noncomputable def cyclesCoToCycles
    [S.shortComplex₁.HasRightHomology] [S.shortComplex₂.HasLeftHomology] :
    S.shortComplex₁.cyclesCo ⟶ S.shortComplex₂.cycles :=
  S.cokerToKer' _ _ (S.shortComplex₁.cyclesCoIsCokernel) (S.shortComplex₂.cyclesIsKernel)

@[reassoc (attr := simp)]
lemma cyclesCoToCycles_fac
    [S.shortComplex₁.HasRightHomology] [S.shortComplex₂.HasLeftHomology] :
    S.shortComplex₁.pCyclesCo ≫ S.cyclesCoToCycles ≫ S.shortComplex₂.iCycles = S.g :=
  S.cokerToKer'_fac _ _ (S.shortComplex₁.cyclesCoIsCokernel) (S.shortComplex₂.cyclesIsKernel)

end

section

variable (S T : ShortComplex C) (e : S.X₃ ≅ T.X₁) (φ : S.X₂ ⟶ T.X₂) (hφ : φ = S.g ≫ e.hom ≫ T.f)

@[simps]
def connectShortComplex : ShortComplex₄ C where
  X₁ := S.X₁
  X₂ := S.X₂
  X₃ := T.X₂
  X₄ := T.X₃
  f := S.f
  g := φ
  h := T.g
  zero₁ := by simp [hφ]
  zero₂ := by simp [hφ]

@[simps]
def connectShortComplexι : S ⟶ (connectShortComplex S T e φ hφ).shortComplex₁ where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := e.hom ≫ T.f

instance : IsIso (connectShortComplexι S T e φ hφ).τ₁ := by dsimp ; infer_instance
instance : IsIso (connectShortComplexι S T e φ hφ).τ₂ := by dsimp ; infer_instance
instance [Mono T.f] : Mono (connectShortComplexι S T e φ hφ).τ₃ := mono_comp _ _

@[simps]
def connectShortComplexπ : (connectShortComplex S T e φ hφ).shortComplex₂ ⟶ T where
  τ₁ := S.g ≫ e.hom
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _

instance [Epi S.g] : Epi (connectShortComplexπ S T e φ hφ).τ₁ := epi_comp _ _
instance : IsIso (connectShortComplexπ S T e φ hφ).τ₂ := by dsimp ; infer_instance
instance : IsIso (connectShortComplexπ S T e φ hφ).τ₃ := by dsimp ; infer_instance

lemma connectShortComplex_exact (hS : S.Exact) (hT : T.Exact) [Epi S.g] [Mono T.f] :
    (connectShortComplex S T e φ hφ).Exact where
  exact₁ := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (connectShortComplexι S T e φ hφ)).1 hS
  exact₂ := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (connectShortComplexπ S T e φ hφ)).2 hT

end

end

section Preadditive

variable {C}
variable [Preadditive C] (S : ShortComplex₄ C)
  (hS : S.Exact) (cc : CokernelCofork S.f) (kf : KernelFork S.h)
  (hcc : IsColimit cc) (hkf : IsLimit kf)

lemma epi_cokerToKer' (hS : S.shortComplex₂.Exact) :
    Epi (S.cokerToKer' cc kf hcc hkf) := by
  have := hS.hasZeroObject
  have := hS.hasHomology
  have : Epi cc.π := ⟨fun _ _ => Cofork.IsColimit.hom_ext hcc⟩
  let h := (hS.leftHomologyDataOfIsLimitKernelFork kf hkf)
  have := h.exact_iff_epi_f'.1 hS
  have fac : cc.π ≫ S.cokerToKer' cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i, h.f'_i, ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i,
      Category.assoc, cokerToKer'_fac, shortComplex₂_f]
  exact epi_of_epi_fac fac

lemma mono_cokerToKer' (hS : S.shortComplex₁.Exact) :
    Mono (S.cokerToKer' cc kf hcc hkf) := by
  have := hS.hasZeroObject
  have := hS.hasHomology
  have : Mono kf.ι := ⟨fun _ _ => Fork.IsLimit.hom_ext hkf⟩
  let h := (hS.rightHomologyDataOfIsColimitCokernelCofork cc hcc)
  have := h.exact_iff_mono_g'.1 hS
  have fac : S.cokerToKer' cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p, h.p_g', ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork_p,
      cokerToKer'_fac, shortComplex₁_g]
  exact mono_of_mono_fac fac

variable {S}
variable [Balanced C]

lemma Exact.isIso_cokerToKer' : IsIso (S.cokerToKer' cc kf hcc hkf) := by
  have := S.mono_cokerToKer' cc kf hcc hkf hS.exact₁
  have := S.epi_cokerToKer' cc kf hcc hkf hS.exact₂
  apply isIso_of_mono_of_epi

lemma Exact.isIso_cokerToKer [HasCokernel S.f] [HasKernel S.h] :
    IsIso S.cokerToKer :=
  hS.isIso_cokerToKer' _ _ _ _

lemma Exact.isIso_cyclesCoToCycles
    [S.shortComplex₁.HasRightHomology] [S.shortComplex₂.HasLeftHomology] :
    IsIso S.cyclesCoToCycles :=
  hS.isIso_cokerToKer' _ _ _ _

@[simps! hom]
noncomputable def Exact.cokerIsoKer' : cc.pt ≅ kf.pt :=
  have := hS.isIso_cokerToKer' cc kf hcc hkf
  asIso (S.cokerToKer' cc kf hcc hkf)

@[simps! hom]
noncomputable def Exact.cokerIsoKer [HasCokernel S.f] [HasKernel S.h] :
    cokernel S.f ≅ kernel S.h :=
  have := hS.isIso_cokerToKer
  asIso S.cokerToKer

@[simps! hom]
lemma Exact.cyclesCoIsoCycles
    [S.shortComplex₁.HasRightHomology] [S.shortComplex₂.HasLeftHomology] :
    S.shortComplex₁.cyclesCo ≅ S.shortComplex₂.cycles :=
  have := hS.isIso_cyclesCoToCycles
  asIso S.cyclesCoToCycles

end Preadditive

end ShortComplex₄

end CategoryTheory
