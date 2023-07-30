/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.RightHomology

/-! Homology of short complexes

In this file, we shall define the homology of short complexes `S`, i.e. diagrams
`f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`. We shall say that
`[S.HasHomology]` when there exists `h : S.HomologyData` (TODO). A homology data
for `S` consists of compatible left/right homology data `left` and `right`. The
left homology data `left` involves an object `left.H` that is a cokernel of the canonical
map `S.X₁ ⟶ K` where `K` is a kernel of `g`. On the other hand, the dual notion `right.H`
is a kernel of the canonical morphism `Q ⟶ S.X₃` when `Q` is a cokernel of `f`.
The compatibility that is required involves an isomorphism `left.H ≅ right.H` which
makes a certain pentagon commute.

This definition requires very little assumption on the category (only the existence
of zero morphisms). We shall prove that in abelian categories, all short complexes
have homology data.

Note: This definition arose by the end of the Liquid Tensor Experiment which
contained a structure `has_homology` which is quite similar to `S.HomologyData`.
After the category `ShortComplex C` was introduced by J. Riou, A. Topaz suggested
such a structure could be used as a basis for the *definition* of homology.

-/

namespace CategoryTheory

open Category Limits

variable {C D : Type _} [Category C] [Category D]
  [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ S₄ : ShortComplex C}

namespace ShortComplex

/-- A homology data for a short complex consists of two compatible left and
right homology data -/
structure HomologyData where
  left : S.LeftHomologyData
  right : S.RightHomologyData
  /-- the compatibility isomorphism relating the two dual notions of
    `LeftHomologyData` and `RightHomologyData`  -/
  iso : left.H ≅ right.H
  comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p := by aesop_cat

attribute [reassoc (attr := simp)] HomologyData.comm

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

structure HomologyMapData :=
(left : LeftHomologyMapData φ h₁.left h₂.left)
(right : RightHomologyMapData φ h₁.right h₂.right)

namespace HomologyMapData

attribute [nolint simpNF] mk.injEq

variable {φ h₁ h₂}

@[reassoc]
lemma comm (h : HomologyMapData φ h₁ h₂) :
    h.left.φH ≫ h₂.iso.hom = h₁.iso.hom ≫ h.right.φH := by
  simp only [← cancel_epi h₁.left.π, ← cancel_mono h₂.right.ι, assoc,
    LeftHomologyMapData.commπ_assoc, HomologyData.comm, LeftHomologyMapData.commi_assoc,
    RightHomologyMapData.commι, HomologyData.comm_assoc, RightHomologyMapData.commp]

instance : Subsingleton (HomologyMapData φ h₁ h₂) := ⟨by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩
  simp only [mk.injEq, eq_iff_true_of_subsingleton, and_self]⟩

instance : Inhabited (HomologyMapData φ h₁ h₂) :=
  ⟨⟨default, default⟩⟩

instance : Unique (HomologyMapData φ h₁ h₂) := Unique.mk' _

variable (φ h₁ h₂)

def some : HomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}

lemma congr_left_φH {γ₁ γ₂ : HomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) :
  γ₁.left.φH = γ₂.left.φH := by rw [eq]

end HomologyMapData

namespace HomologyData

@[simps]
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    S.HomologyData where
  left := LeftHomologyData.ofIsLimitKernelFork S hf c hc
  right := RightHomologyData.ofIsLimitKernelFork S hf c hc
  iso := Iso.refl _

@[simps]
noncomputable def ofHasKernel (hf : S.f = 0) [HasKernel S.g] :
    S.HomologyData where
  left := LeftHomologyData.ofHasKernel S hf
  right := RightHomologyData.ofHasKernel S hf
  iso := Iso.refl _

@[simps]
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
    S.HomologyData where
  left := LeftHomologyData.ofIsColimitCokernelCofork S hg c hc
  right := RightHomologyData.ofIsColimitCokernelCofork S hg c hc
  iso := Iso.refl _

@[simps]
noncomputable def ofHasCokernel (hg : S.g = 0) [HasCokernel S.f] :
    S.HomologyData where
  left := LeftHomologyData.ofHasCokernel S hg
  right := RightHomologyData.ofHasCokernel S hg
  iso := Iso.refl _

@[simps]
noncomputable def ofZeros (hf : S.f = 0) (hg : S.g = 0) :
    S.HomologyData where
  left := LeftHomologyData.ofZeros S hf hg
  right := RightHomologyData.ofZeros S hf hg
  iso := Iso.refl _

@[simps]
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HomologyData S₂ where
  left := LeftHomologyData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono φ h.right
  iso := h.iso

@[simps]
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HomologyData S₁ where
  left := LeftHomologyData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono' φ h.right
  iso := h.iso

@[simps!]
noncomputable def ofIso (e : S₁ ≅ S₂) (h : HomologyData S₁) :=
  h.ofEpiOfIsIsoOfMono e.hom

variable {S}

@[simps]
def op (h : S.HomologyData) : S.op.HomologyData where
  left := h.right.op
  right := h.left.op
  iso := h.iso.op
  comm := Quiver.Hom.unop_inj (by simp)

@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.HomologyData) : S.unop.HomologyData where
  left := h.right.unop
  right := h.left.unop
  iso := h.iso.unop
  comm := Quiver.Hom.op_inj (by simp)

end HomologyData

class HasHomology : Prop where
  condition : Nonempty S.HomologyData

noncomputable def homologyData [HasHomology S] :
  S.HomologyData := HasHomology.condition.some

variable {S}

lemma HasHomology.mk' (h : S.HomologyData) : HasHomology S :=
  ⟨Nonempty.intro h⟩

instance [HasHomology S] : HasHomology S.op :=
  HasHomology.mk' S.homologyData.op

instance hasLeftHomology_of_hasHomology [S.HasHomology] : S.HasLeftHomology :=
  HasLeftHomology.mk' S.homologyData.left

instance hasRightHomology_of_hasHomology [S.HasHomology] : S.HasRightHomology :=
  HasRightHomology.mk' S.homologyData.right

instance hasHomology_of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasHomology :=
  HasHomology.mk' (HomologyData.ofHasCokernel _ rfl)

instance hasHomology_of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasHomology :=
  HasHomology.mk' (HomologyData.ofHasKernel _ rfl)

instance hasHomology_of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasHomology :=
  HasHomology.mk' (HomologyData.ofZeros _ rfl rfl)

lemma hasHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₂ :=
  HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono φ S₁.homologyData)

lemma hasHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₁ :=
  HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono' φ S₂.homologyData)

lemma hasHomology_of_iso (e : S₁ ≅ S₂) [HasHomology S₁] : HasHomology S₂ :=
  HasHomology.mk' (HomologyData.ofIso e S₁.homologyData)

namespace HomologyMapData

@[simps]
def id (h : S.HomologyData) : HomologyMapData (𝟙 S) h h where
  left := LeftHomologyMapData.id h.left
  right := RightHomologyMapData.id h.right

@[simps]
def zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
  HomologyMapData 0 h₁ h₂ where
  left := LeftHomologyMapData.zero h₁.left h₂.left
  right := RightHomologyMapData.zero h₁.right h₂.right

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.HomologyData}
    {h₂ : S₂.HomologyData} {h₃ : S₃.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) (ψ' : HomologyMapData φ' h₂ h₃) :
    HomologyMapData (φ ≫ φ') h₁ h₃ where
  left := ψ.left.comp ψ'.left
  right := ψ.right.comp ψ'.right

@[simps]
def op {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (opMap φ) h₂.op h₁.op where
  left := ψ.right.op
  right := ψ.left.op

@[simps]
def unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (unopMap φ) h₂.unop h₁.unop where
  left := ψ.right.unop
  right := ψ.left.unop

@[simps]
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    HomologyMapData φ (HomologyData.ofZeros S₁ hf₁ hg₁) (HomologyData.ofZeros S₂ hf₂ hg₂) where
  left := LeftHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂
  right := RightHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂

@[simps]
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
  (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
  (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
  HomologyMapData φ (HomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
    (HomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm

@[simps]
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
  (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
  (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
  HomologyMapData φ (HomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
    (HomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm

def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
  (c : CokernelCofork S.f) (hc : IsColimit c) :
  HomologyMapData (𝟙 S) (HomologyData.ofZeros S hf hg)
    (HomologyData.ofIsColimitCokernelCofork S hg c hc) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc

@[simps]
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
  (c : KernelFork S.g) (hc : IsLimit c) :
  HomologyMapData (𝟙 S)
    (HomologyData.ofIsLimitKernelFork S hf c hc)
    (HomologyData.ofZeros S hf hg) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc

noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ h (HomologyData.ofEpiOfIsIsoOfMono φ h) where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono φ h.right

noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ (HomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono' φ h.right

end HomologyMapData

variable (S)

noncomputable def homology [HasHomology S] : C := S.homologyData.left.H

noncomputable def leftHomologyIso [S.HasHomology] : S.leftHomology ≅ S.homology :=
  leftHomologyMapIso' (Iso.refl _) _ _

noncomputable def rightHomologyIso [S.HasHomology] : S.rightHomology ≅ S.homology :=
  rightHomologyMapIso' (Iso.refl _) _ _ ≪≫ S.homologyData.iso.symm

variable {S}

noncomputable def LeftHomologyData.homologyIso (h : S.LeftHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.leftHomologyIso.symm ≪≫ h.leftHomologyIso

noncomputable def RightHomologyData.homologyIso (h : S.RightHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.rightHomologyIso.symm ≪≫ h.rightHomologyIso

variable (S)

@[simp]
lemma LeftHomologyData.homologyIso_leftHomologyData [S.HasHomology] :
    S.leftHomologyData.homologyIso = S.leftHomologyIso.symm := by
  ext
  dsimp only [homologyIso, Iso.symm, Iso.trans, leftHomologyIso, ShortComplex.leftHomologyIso,
    Iso.refl, leftHomologyMapIso']
  rw [← leftHomologyMap'_comp, comp_id]

@[simp]
lemma RightHomologyData.homologyIso_rightHomologyData [S.HasHomology] :
    S.rightHomologyData.homologyIso = S.rightHomologyIso.symm := by
  ext
  dsimp only [homologyIso, Iso.symm, Iso.trans, Iso.refl, ShortComplex.rightHomologyIso,
    rightHomologyMapIso', rightHomologyIso]
  erw [rightHomologyMap'_id, comp_id]

variable {S}

def homologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
  h₁.left.H ⟶ h₂.left.H := leftHomologyMap' φ _ _

noncomputable def homologyMap (φ : S₁ ⟶ S₂) [HasHomology S₁] [HasHomology S₂] :
    S₁.homology ⟶ S₂.homology :=
  homologyMap' φ _ _

namespace HomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
  (γ : HomologyMapData φ h₁ h₂)

lemma homologyMap'_eq : homologyMap' φ h₁ h₂ = γ.left.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

lemma cyclesMap'_eq : cyclesMap' φ h₁.left h₂.left = γ.left.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

lemma opcyclesMap'_eq : opcyclesMap' φ h₁.right h₂.right = γ.right.φQ :=
  RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

end HomologyMapData

namespace LeftHomologyMapData

variable {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

lemma homologyMap_eq :
    homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp only [homologyMap, LeftHomologyData.homologyIso,
    Iso.trans, Iso.symm, leftHomologyIso, LeftHomologyData.leftHomologyIso,
    leftHomologyMapIso', homologyMap', Iso.refl]
  simp only [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp, id_comp, comp_id]

lemma homologyMap_comm :
    homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH := by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

end LeftHomologyMapData

namespace RightHomologyMapData

variable {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

lemma homologyMap_eq :
    homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp only [homologyMap, homologyMap', RightHomologyData.homologyIso, Iso.symm, Iso.trans,
    Iso.refl, rightHomologyIso, rightHomologyMapIso', RightHomologyData.rightHomologyIso]
  have γ' : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  simp only [← γ.rightHomologyMap'_eq, assoc, ← rightHomologyMap'_comp_assoc,
    id_comp, comp_id, γ'.left.leftHomologyMap'_eq, γ'.right.rightHomologyMap'_eq, ← γ'.comm_assoc,
    Iso.hom_inv_id]

lemma homologyMap_comm :
    homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH := by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

end RightHomologyMapData

@[simp]
lemma homologyMap'_id (h : S.HomologyData) :
    homologyMap' (𝟙 S) h h = 𝟙 _ :=
  (HomologyMapData.id h).homologyMap'_eq

variable (S)

@[simp]
lemma homologyMap_id [HasHomology S] :
    homologyMap (𝟙 S) = 𝟙 _ :=
  homologyMap'_id _

@[simp]
lemma homologyMap'_zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    homologyMap' 0 h₁ h₂ = 0 :=
  (HomologyMapData.zero h₁ h₂).homologyMap'_eq

variable (S₁ S₂)

@[simp]
lemma homologyMap_zero [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (0 : S₁ ⟶ S₂) = 0 :=
  homologyMap'_zero _ _

variable {S₁ S₂}

lemma homologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) (h₃ : S₃.HomologyData) :
    homologyMap' (φ₁ ≫ φ₂) h₁ h₃ = homologyMap' φ₁ h₁ h₂ ≫
      homologyMap' φ₂ h₂ h₃ :=
  leftHomologyMap'_comp _ _ _ _ _

@[simp]
lemma homologyMap_comp [HasHomology S₁] [HasHomology S₂] [HasHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    homologyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫ homologyMap φ₂ :=
homologyMap'_comp _ _ _ _ _

@[simps]
def homologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.HomologyData)
    (h₂ : S₂.HomologyData) : h₁.left.H ≅ h₂.left.H where
  hom := homologyMap' e.hom h₁ h₂
  inv := homologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← homologyMap'_comp, e.hom_inv_id, homologyMap'_id]
  inv_hom_id := by rw [← homologyMap'_comp, e.inv_hom_id, homologyMap'_id]

instance isIso_homologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    IsIso (homologyMap' φ h₁ h₂) :=
  (inferInstance : IsIso (homologyMapIso' (asIso φ) h₁ h₂).hom)

@[simps]
noncomputable def homologyMapIso (e : S₁ ≅ S₂) [S₁.HasHomology]
  [S₂.HasHomology] : S₁.homology ≅ S₂.homology where
  hom := homologyMap e.hom
  inv := homologyMap e.inv
  hom_inv_id := by rw [← homologyMap_comp, e.hom_inv_id, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, e.inv_hom_id, homologyMap_id]

instance isIso_homologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasHomology]
    [S₂.HasHomology] :
    IsIso (homologyMap φ) :=
  (inferInstance : IsIso (homologyMapIso (asIso φ)).hom)

variable {S}

def leftRightHomologyComparison' (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    h₁.H ⟶ h₂.H :=
  h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
      RightHomologyData.p_g', LeftHomologyData.wi, comp_zero])

lemma leftRightHomologyComparison'_eq₁ (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ =
  h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
      RightHomologyData.p_g', LeftHomologyData.wi, comp_zero]) := rfl

@[reassoc (attr := simp)]
lemma π_leftRightHomologyComparison'_ι (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    h₁.π ≫ leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι = h₁.i ≫ h₂.p :=
  by simp only [leftRightHomologyComparison'_eq₁,
    RightHomologyData.liftH_ι, LeftHomologyData.π_descH]

lemma leftRightHomologyComparison'_eq₂ (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ =
  h₁.descH (h₂.liftH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_mono h₂.ι, assoc, RightHomologyData.liftH_ι,
      LeftHomologyData.f'_i_assoc, RightHomologyData.wp, zero_comp]) := by
  simp only [← cancel_mono h₂.ι, ← cancel_epi h₁.π, π_leftRightHomologyComparison'_ι,
    LeftHomologyData.π_descH_assoc, RightHomologyData.liftH_ι]

variable (S)

noncomputable def leftRightHomologyComparison [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomology ⟶ S.rightHomology :=
  leftRightHomologyComparison' _ _

@[reassoc (attr := simp)]
lemma π_leftRightHomologyComparison_ι [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomologyπ ≫ S.leftRightHomologyComparison ≫ S.rightHomologyι =
      S.iCycles ≫ S.pOpcycles :=
  π_leftRightHomologyComparison'_ι _ _

@[reassoc]
lemma leftRightHomologyComparison'_naturality (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData)
  (h₂ : S₁.RightHomologyData) (h₁' : S₂.LeftHomologyData) (h₂' : S₂.RightHomologyData) :
  leftHomologyMap' φ h₁ h₁' ≫ leftRightHomologyComparison' h₁' h₂' =
    leftRightHomologyComparison' h₁ h₂ ≫ rightHomologyMap' φ h₂ h₂' :=
by simp only [← cancel_epi h₁.π, ← cancel_mono h₂'.ι, assoc,
    leftHomologyπ_naturality'_assoc, rightHomologyι_naturality',
    π_leftRightHomologyComparison'_ι,
    π_leftRightHomologyComparison'_ι_assoc,
    cyclesMap'_i_assoc, p_opcyclesMap']

variable {S}

lemma leftRightHomologyComparison'_compatibility (h₁ h₁' : S.LeftHomologyData)
    (h₂ h₂' : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ = leftHomologyMap' (𝟙 S) h₁ h₁' ≫
      leftRightHomologyComparison' h₁' h₂' ≫ rightHomologyMap' (𝟙 S) _ _ :=
by rw [leftRightHomologyComparison'_naturality_assoc (𝟙 S) h₁ h₂ h₁' h₂',
    ← rightHomologyMap'_comp, comp_id, rightHomologyMap'_id, comp_id]

lemma leftRightHomologyComparison_eq [S.HasLeftHomology] [S.HasRightHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    S.leftRightHomologyComparison = h₁.leftHomologyIso.hom ≫
      leftRightHomologyComparison' h₁ h₂ ≫ h₂.rightHomologyIso.inv :=
leftRightHomologyComparison'_compatibility _ _ _ _

@[simp]
lemma HomologyData.leftRightHomologyComparison'_eq (h : S.HomologyData) :
    leftRightHomologyComparison' h.left h.right = h.iso.hom := by
  simp only [←cancel_epi h.left.π, ← cancel_mono h.right.ι,
    π_leftRightHomologyComparison'_ι, HomologyData.comm]

instance isIso_leftRightHomologyComparison'_of_homologyData (h : S.HomologyData) :
  IsIso (leftRightHomologyComparison' h.left h.right) := by
    rw [h.leftRightHomologyComparison'_eq]
    infer_instance

instance isIso_leftRightHomologyComparison' [S.HasHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    IsIso (leftRightHomologyComparison' h₁ h₂) := by
  rw [leftRightHomologyComparison'_compatibility h₁ S.homologyData.left h₂
    S.homologyData.right]
  infer_instance

instance isIso_leftRightHomologyComparison [S.HasHomology] :
    IsIso S.leftRightHomologyComparison := by
  dsimp only [leftRightHomologyComparison]
  infer_instance

namespace HomologyData

@[simps]
noncomputable def ofIsIsoLeftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (leftRightHomologyComparison' h₁ h₂)] :
    S.HomologyData where
  left := h₁
  right := h₂
  iso := asIso (leftRightHomologyComparison' h₁ h₂)

end HomologyData

variable (S)

noncomputable def homologyData' [S.HasHomology] : S.HomologyData :=
  HomologyData.ofIsIsoLeftRightHomologyComparison'
    S.leftHomologyData S.rightHomologyData

variable {S}

lemma leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomology_map'
    (h : S.HomologyData) (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ =
      leftHomologyMap' (𝟙 S) h₁ h.left ≫ h.iso.hom ≫ rightHomologyMap' (𝟙 S) h.right h₂ := by
  simpa only [h.leftRightHomologyComparison'_eq] using leftRightHomologyComparison'_compatibility h₁ h.left h₂ h.right

@[reassoc]
lemma leftRightHomologyComparison'_fac (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [S.HasHomology] :
    leftRightHomologyComparison' h₁ h₂ = h₁.homologyIso.inv ≫ h₂.homologyIso.hom := by
  rw [leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomology_map'
    S.homologyData h₁ h₂]
  dsimp only [LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyMapIso', leftHomologyIso,
    RightHomologyData.homologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', rightHomologyIso]
  simp only [assoc, ← leftHomologyMap'_comp_assoc, id_comp, ← rightHomologyMap'_comp]

variable (S)

@[reassoc]
lemma leftRightHomologyComparison_fac [S.HasHomology] :
    S.leftRightHomologyComparison = S.leftHomologyIso.hom ≫ S.rightHomologyIso.inv := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv,
    RightHomologyData.homologyIso_rightHomologyData, Iso.symm_hom] using
      leftRightHomologyComparison'_fac S.leftHomologyData S.rightHomologyData

variable {S}

lemma hasHomology_of_isIso_leftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (leftRightHomologyComparison' h₁ h₂)] :
    S.HasHomology :=
  HasHomology.mk' (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂)

lemma hasHomology_of_isIsoLeftRightHomologyComparison [S.HasLeftHomology]
    [S.HasRightHomology] [h : IsIso S.leftRightHomologyComparison] :
    S.HasHomology := by
  haveI : IsIso (leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData) := h
  exact hasHomology_of_isIso_leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData

@[reassoc]
lemma LeftHomologyData.leftHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.homologyIso.hom ≫ leftHomologyMap' φ h₁ h₂ =
      homologyMap φ ≫ h₂.homologyIso.hom := by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

@[reassoc]
lemma LeftHomologyData.leftHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
      h₁.homologyIso.inv ≫ homologyMap φ =
       leftHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

@[reassoc]
lemma leftHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.leftHomologyIso.hom ≫ homologyMap φ =
      leftHomologyMap φ ≫ S₂.leftHomologyIso.hom := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using
    LeftHomologyData.leftHomologyIso_inv_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]
lemma leftHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.leftHomologyIso.inv ≫ leftHomologyMap φ =
      homologyMap φ ≫ S₂.leftHomologyIso.inv := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using
    LeftHomologyData.leftHomologyIso_hom_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]
lemma RightHomologyData.rightHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.homologyIso.hom ≫ rightHomologyMap' φ h₁ h₂ =
      homologyMap φ ≫ h₂.homologyIso.hom := by
  rw [← cancel_epi h₁.homologyIso.inv, Iso.inv_hom_id_assoc,
    ← cancel_epi (leftRightHomologyComparison' S₁.leftHomologyData h₁),
    ← leftRightHomologyComparison'_naturality φ S₁.leftHomologyData h₁ S₂.leftHomologyData h₂,
    ← cancel_epi (S₁.leftHomologyData.homologyIso.hom),
    LeftHomologyData.leftHomologyIso_hom_naturality_assoc,
    leftRightHomologyComparison'_fac, leftRightHomologyComparison'_fac, assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

@[reassoc]
lemma RightHomologyData.rightHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
      h₁.homologyIso.inv ≫ homologyMap φ =
        rightHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  simp only [← cancel_mono h₂.homologyIso.hom, assoc,
    ← RightHomologyData.rightHomologyIso_hom_naturality φ h₁ h₂, Iso.inv_hom_id,
    Iso.inv_hom_id_assoc, comp_id]

@[reassoc]
lemma rightHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.rightHomologyIso.hom ≫ homologyMap φ =
      rightHomologyMap φ ≫ S₂.rightHomologyIso.hom := by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using
    RightHomologyData.rightHomologyIso_inv_naturality φ S₁.rightHomologyData S₂.rightHomologyData

@[reassoc]
lemma rightHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.rightHomologyIso.inv ≫ rightHomologyMap φ =
      homologyMap φ ≫ S₂.rightHomologyIso.inv := by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using
    RightHomologyData.rightHomologyIso_hom_naturality φ S₁.rightHomologyData S₂.rightHomologyData

variable (C)

class _root_.CategoryTheory.CategoryWithHomology : Prop where
  hasHomology : ∀ (S : ShortComplex C), S.HasHomology

attribute [instance] CategoryWithHomology.hasHomology

instance [CategoryWithHomology C] : CategoryWithHomology Cᵒᵖ :=
  ⟨fun S => HasHomology.mk' S.unop.homologyData.op⟩

@[simps]
noncomputable def homologyFunctor [CategoryWithHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.homology
  map f := homologyMap f

variable {C}

instance isIso_homologyMap'_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (homologyMap' φ h₁ h₂) := by
  dsimp only [homologyMap']
  infer_instance

lemma isIso_homologyMap_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
    (h₁ : Epi φ.τ₁) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃) :
    IsIso (homologyMap φ) := by
  dsimp only [homologyMap]
  infer_instance

instance isIso_homologyMap_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (homologyMap φ) :=
  isIso_homologyMap_of_epi_of_isIso_of_mono' φ inferInstance inferInstance inferInstance

instance isIso_homologyFunctor_map_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [CategoryWithHomology C]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso ((homologyFunctor C).map φ) :=
  (inferInstance : IsIso (homologyMap φ))

instance isIso_homologyMap_of_isIso (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] [IsIso φ] :
    IsIso (homologyMap φ) := by
  dsimp only [homologyMap, homologyMap']
  infer_instance

section

variable (S) {A : C}
variable [HasHomology S]

noncomputable def homologyπ : S.cycles ⟶ S.homology :=
  S.leftHomologyπ ≫ S.leftHomologyIso.hom

noncomputable def homologyι : S.homology ⟶ S.opcycles :=
  S.rightHomologyIso.inv ≫ S.rightHomologyι

@[reassoc (attr := simp)]
lemma homologyπ_comp_leftHomologyIso_inv:
    S.homologyπ ≫ S.leftHomologyIso.inv = S.leftHomologyπ := by
  dsimp only [homologyπ]
  simp only [assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
lemma rightHomologyIso_hom_comp_homologyι :
    S.rightHomologyIso.hom ≫ S.homologyι = S.rightHomologyι := by
  dsimp only [homologyι]
  simp only [Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma toCycles_comp_homologyπ :
    S.toCycles ≫ S.homologyπ = 0 := by
  dsimp only [homologyπ]
  simp only [toCycles_comp_leftHomologyπ_assoc, zero_comp]

@[reassoc (attr := simp)]
lemma homologyι_comp_fromOpcycles :
    S.homologyι ≫ S.fromOpcycles = 0 := by
  dsimp only [homologyι]
  simp only [assoc, rightHomologyι_comp_fromOpcycles, comp_zero]

noncomputable def homologyIsCokernel :
  IsColimit (CokernelCofork.ofπ S.homologyπ S.toCycles_comp_homologyπ) :=
IsColimit.ofIsoColimit S.leftHomologyIsCokernel
  (Cofork.ext S.leftHomologyIso rfl)

noncomputable def homologyIsKernel :
  IsLimit (KernelFork.ofι S.homologyι S.homologyι_comp_fromOpcycles) :=
IsLimit.ofIsoLimit S.rightHomologyIsKernel
  (Fork.ext S.rightHomologyIso (by simp))

instance : Epi S.homologyπ :=
  Limits.epi_of_isColimit_cofork (S.homologyIsCokernel)

instance : Mono S.homologyι :=
  Limits.mono_of_isLimit_fork (S.homologyIsKernel)

noncomputable def descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
    S.homology ⟶ A :=
  S.homologyIsCokernel.desc (CokernelCofork.ofπ k hk)

noncomputable def liftHomology (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0) :
    A ⟶ S.homology :=
  S.homologyIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma π_descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
  S.homologyπ ≫ S.descHomology k hk = k :=
Cofork.IsColimit.π_desc S.homologyIsCokernel

@[reassoc (attr := simp)]
lemma liftHomology_ι (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0) :
  S.liftHomology k hk ≫ S.homologyι = k :=
  Fork.IsLimit.lift_ι S.homologyIsKernel

@[reassoc (attr := simp)]
lemma homologyπ_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    S₁.homologyπ ≫ homologyMap φ = cyclesMap φ ≫ S₂.homologyπ := by
  simp only [← cancel_mono S₂.leftHomologyIso.inv, assoc, ← leftHomologyIso_inv_naturality φ,
    homologyπ_comp_leftHomologyIso_inv, ← leftHomologyπ_naturality]
  simp only [homologyπ, assoc, Iso.hom_inv_id_assoc, leftHomologyπ_naturality]

@[reassoc (attr := simp)]
lemma homologyι_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap φ ≫ S₂.homologyι = S₁.homologyι ≫ S₁.opcyclesMap φ  := by
  simp only [← cancel_epi S₁.rightHomologyIso.hom, rightHomologyIso_hom_naturality_assoc φ,
    rightHomologyIso_hom_comp_homologyι, rightHomologyι_naturality]
  simp only [homologyι, assoc, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma homology_π_ι :
    S.homologyπ ≫ S.homologyι = S.iCycles ≫ S.pOpcycles := by
  dsimp only [homologyπ, homologyι]
  simpa only [assoc, S.leftRightHomologyComparison_fac] using S.π_leftRightHomologyComparison_ι

noncomputable def homologyIsoKernelDesc [S.HasHomology] [HasCokernel S.f]
  [HasKernel (cokernel.desc S.f S.g S.zero)] :
  S.homology ≅ kernel (cokernel.desc S.f S.g S.zero) :=
  S.rightHomologyIso.symm ≪≫ S.rightHomologyIsoKernelDesc

noncomputable def homologyIsoCokernelLift [S.HasHomology] [HasKernel S.g]
  [HasCokernel (kernel.lift S.g S.f S.zero)] :
  S.homology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
  S.leftHomologyIso.symm ≪≫ S.leftHomologyIsoCokernelLift

@[reassoc (attr := simp)]
lemma LeftHomologyData.homologyπ_comp_homologyIso_hom
    (h : S.LeftHomologyData) [S.HasHomology] :
    S.homologyπ ≫ h.homologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id_assoc,
    leftHomologyπ_comp_leftHomologyIso_hom]

@[reassoc (attr := simp)]
lemma LeftHomologyData.π_comp_homologyIso_inv (h : S.LeftHomologyData) [S.HasHomology] :
    h.π ≫ h.homologyIso.inv = h.cyclesIso.inv ≫ S.homologyπ := by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, π_comp_leftHomologyIso_inv_assoc]

@[reassoc (attr := simp)]
lemma RightHomologyData.homologyIso_inv_comp_homologyι
    (h : S.RightHomologyData) [S.HasHomology] :
    h.homologyIso.inv ≫ S.homologyι = h.ι ≫ h.opcyclesIso.inv := by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, assoc, Iso.hom_inv_id_assoc,
    rightHomologyIso_inv_comp_rightHomologyι]

@[reassoc (attr := simp)]
lemma RightHomologyData.homologyIso_hom_comp_ι
    (h : S.RightHomologyData) [S.HasHomology] :
    h.homologyIso.hom ≫ h.ι = S.homologyι ≫ h.opcyclesIso.hom := by
  dsimp only [homologyι, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, rightHomologyIso_hom_comp_ι]

@[reassoc (attr := simp)]
lemma LeftHomologyData.homologyIso_hom_comp_leftHomologyIso_inv
    (h : S.LeftHomologyData) [S.HasHomology] :
    h.homologyIso.hom ≫ h.leftHomologyIso.inv =
      S.leftHomologyIso.inv := by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
lemma LeftHomologyData.leftHomologyIso_hom_comp_homologyIso_inv
    (h : S.LeftHomologyData) [S.HasHomology] :
    h.leftHomologyIso.hom ≫ h.homologyIso.inv =
      S.leftHomologyIso.hom := by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma RightHomologyData.homologyIso_hom_comp_rightHomologyIso_inv
    (h : S.RightHomologyData) [S.HasHomology] :
    h.homologyIso.hom ≫ h.rightHomologyIso.inv =
      S.rightHomologyIso.inv := by
  dsimp only [homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
lemma RightHomologyData.rightHomologyIso_hom_comp_homologyIso_inv
    (h : S.RightHomologyData) [S.HasHomology] :
    h.rightHomologyIso.hom ≫ h.homologyIso.inv =
      S.rightHomologyIso.hom := by
  dsimp only [homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.hom_inv_id_assoc]

@[reassoc]
lemma comp_homologyMap_comp [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.π ≫ h₁.homologyIso.inv ≫ homologyMap φ ≫ h₂.homologyIso.hom ≫ h₂.ι =
      h₁.i ≫ φ.τ₂ ≫ h₂.p := by
  dsimp only [LeftHomologyData.homologyIso, RightHomologyData.homologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyIso, rightHomologyIso,
    leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.cyclesIso, RightHomologyData.opcyclesIso,
    LeftHomologyData.leftHomologyIso, RightHomologyData.rightHomologyIso,
    homologyMap, homologyMap']
  simp only [assoc, rightHomologyι_naturality', rightHomologyι_naturality'_assoc,
    leftHomologyπ_naturality'_assoc, HomologyData.comm_assoc, p_opcyclesMap'_assoc,
    id_τ₂, p_opcyclesMap', id_comp, cyclesMap'_i_assoc]

@[reassoc]
lemma π_homologyMap_ι [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.homologyπ ≫ homologyMap φ ≫ S₂.homologyι =
      S₁.iCycles ≫ φ.τ₂ ≫ S₂.pOpcycles := by
  simp only [homologyι_naturality, homology_π_ι_assoc, p_opcyclesMap]

end

variable (S)

noncomputable def homologyOpIso [S.HasHomology] :
    S.op.homology ≅ Opposite.op S.homology :=
  S.op.leftHomologyIso.symm ≪≫ S.leftHomologyOpIso ≪≫ S.rightHomologyIso.symm.op

@[simp]
lemma homologyMap'_op : (homologyMap' φ h₁ h₂).op =
    h₂.iso.inv.op ≫ homologyMap' (opMap φ) h₂.op h₁.op ≫ h₁.iso.hom.op := Quiver.Hom.unop_inj (by
  dsimp
  have γ : HomologyMapData φ h₁ h₂ := default
  simp only [γ.homologyMap'_eq, γ.op.homologyMap'_eq, HomologyData.op_left,
    HomologyMapData.op_left, RightHomologyMapData.op_φH, Quiver.Hom.unop_op, assoc,
    ← γ.comm_assoc, Iso.hom_inv_id, comp_id])

@[simp]
lemma homologyMap_op [HasHomology S₁] [HasHomology S₂] : (homologyMap φ).op =
    (S₂.homologyOpIso).inv ≫ homologyMap (opMap φ) ≫ (S₁.homologyOpIso).hom := by
  dsimp only [homologyMap, homologyOpIso]
  rw [homologyMap'_op]
  dsimp only [Iso.symm, Iso.trans, Iso.op, Iso.refl, rightHomologyIso, leftHomologyIso,
    leftHomologyOpIso, leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.leftHomologyIso, homologyMap']
  simp only [assoc, rightHomologyMap'_op, op_comp, ← leftHomologyMap'_comp_assoc, id_comp,
    opMap_id, comp_id, HomologyData.op_left]

variable (C)

noncomputable def homologyFunctorOpNatIso [CategoryWithHomology C] :
    (homologyFunctor C).op ≅ opFunctor C ⋙ homologyFunctor Cᵒᵖ :=
  NatIso.ofComponents (fun S => Iso.symm S.unop.homologyOpIso) (by simp)

variable {C}

lemma liftCycles_homologyπ_eq_zero_of_boundary [S.HasHomology]
    (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.liftCycles k (by rw [hx, assoc, S.zero, comp_zero]) ≫ S.homologyπ = 0 := by
  dsimp only [homologyπ]
  rw [S.liftCycles_leftHomologyπ_eq_zero_of_boundary_assoc k x hx, zero_comp]

@[reassoc]
lemma homologyι_descOpcycles_π_eq_zero_of_boundary [S.HasHomology]
    (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    S.homologyι ≫ S.descOpcycles k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := by
  dsimp only [homologyι]
  rw [assoc, S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary k x hx, comp_zero]

lemma isIso_homologyMap_of_isIso_cyclesMap_of_epi (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] (h₁ : IsIso (cyclesMap φ)) (h₂ : Epi φ.τ₁) :
    IsIso (homologyMap φ) := by
  have h : S₂.toCycles ≫ inv (cyclesMap φ) ≫ S₁.homologyπ = 0 := by
    simp only [← cancel_epi φ.τ₁, ← toCycles_naturality_assoc,
      IsIso.hom_inv_id_assoc, toCycles_comp_homologyπ, comp_zero]
  have ⟨z, hz⟩ := CokernelCofork.IsColimit.desc' S₂.homologyIsCokernel _ h
  dsimp at hz
  refine' ⟨⟨z, _, _⟩⟩
  . rw [← cancel_epi S₁.homologyπ, homologyπ_naturality_assoc, hz,
      IsIso.hom_inv_id_assoc, comp_id]
  . rw [← cancel_epi S₂.homologyπ, reassoc_of% hz,
      homologyπ_naturality, IsIso.inv_hom_id_assoc, comp_id]

lemma isIso_homologyMap_of_isIso_opcyclesMap_of_mono (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] (h₁ : IsIso (opcyclesMap φ)) (h₂ : Mono φ.τ₃) :
    IsIso (homologyMap φ) := by
  have h : (S₂.homologyι ≫ inv (opcyclesMap φ)) ≫ S₁.fromOpcycles = 0 := by
    simp only [← cancel_mono φ.τ₃, zero_comp, assoc, ← fromOpcycles_naturality,
      IsIso.inv_hom_id_assoc, homologyι_comp_fromOpcycles]
  have ⟨z, hz⟩ := KernelFork.IsLimit.lift' S₁.homologyIsKernel _ h
  dsimp at hz
  refine' ⟨⟨z, _, _⟩⟩
  . rw [← cancel_mono S₁.homologyι, id_comp, assoc, hz, homologyι_naturality_assoc,
      IsIso.hom_inv_id, comp_id]
  . rw [← cancel_mono S₂.homologyι, assoc, homologyι_naturality, reassoc_of% hz,
      IsIso.inv_hom_id, comp_id, id_comp]

lemma isZero_homology_of_isZero_X₂ (hS : IsZero S.X₂) [S.HasHomology] :
    IsZero S.homology :=
  IsZero.of_iso hS (HomologyData.ofZeros S (hS.eq_of_tgt _ _)
    (hS.eq_of_src _ _)).left.homologyIso


lemma isIso_homologyπ (hf : S.f = 0) [S.HasHomology] :
    IsIso S.homologyπ := by
  have := S.isIso_leftHomologyπ hf
  dsimp only [homologyπ]
  infer_instance

lemma isIso_homologyι (hg : S.g = 0) [S.HasHomology] :
    IsIso S.homologyι := by
  have := S.isIso_rightHomologyι hg
  dsimp only [homologyι]
  infer_instance

@[simps! hom]
noncomputable def asIsoHomologyπ (hf : S.f = 0) [S.HasHomology] :
    S.cycles ≅ S.homology := by
  have := S.isIso_homologyπ hf
  exact asIso S.homologyπ

@[reassoc (attr := simp)]
lemma asIsoHomologyπ_inv_comp_homologyπ (hf : S.f = 0) [S.HasHomology] :
  (S.asIsoHomologyπ hf).inv ≫ S.homologyπ = 𝟙 _ := Iso.inv_hom_id _

@[reassoc (attr := simp)]
lemma homologyπ_comp_asIsoHomologyπ_inv (hf : S.f = 0) [S.HasHomology] :
  S.homologyπ ≫ (S.asIsoHomologyπ hf).inv  = 𝟙 _ := (S.asIsoHomologyπ hf).hom_inv_id

@[simps! hom]
noncomputable def asIsoHomologyι (hg : S.g = 0) [S.HasHomology] :
    S.homology ≅ S.opcycles := by
  have := S.isIso_homologyι hg
  exact asIso S.homologyι

@[reassoc (attr := simp)]
lemma asIsoHomologyι_inv_comp_homologyι (hg : S.g = 0) [S.HasHomology] :
  (S.asIsoHomologyι hg).inv ≫ S.homologyι = 𝟙 _ := Iso.inv_hom_id _

@[reassoc (attr := simp)]
lemma homologyι_comp_asIsoHomologyι_inv (hg : S.g = 0) [S.HasHomology] :
  S.homologyι ≫ (S.asIsoHomologyι hg).inv  = 𝟙 _ := (S.asIsoHomologyι hg).hom_inv_id

lemma mono_homologyMap_of_mono_opcyclesMap' [S₁.HasHomology] [S₂.HasHomology]
    (h : Mono (opcyclesMap φ)) :
    Mono (homologyMap φ) := by
  have : Mono (homologyMap φ ≫ S₂.homologyι) := by
    rw [homologyι_naturality φ]
    apply mono_comp
  exact mono_of_mono (homologyMap φ) S₂.homologyι

instance mono_homologyMap_of_mono_opcyclesMap [S₁.HasHomology] [S₂.HasHomology]
    [Mono (opcyclesMap φ)] :
    Mono (homologyMap φ) :=
  mono_homologyMap_of_mono_opcyclesMap' φ inferInstance

lemma epi_homologyMap_of_epi_cyclesMap' [S₁.HasHomology] [S₂.HasHomology]
    (h : Epi (cyclesMap φ)) :
    Epi (homologyMap φ) := by
  have : Epi (S₁.homologyπ ≫ homologyMap φ) := by
    rw [homologyπ_naturality φ]
    apply epi_comp
  exact epi_of_epi S₁.homologyπ (homologyMap φ)

instance epi_homologyMap_of_epi_cyclesMap [S₁.HasHomology] [S₂.HasHomology]
    [Epi (cyclesMap φ)] :
    Epi (homologyMap φ) :=
  epi_homologyMap_of_epi_cyclesMap' φ inferInstance

end ShortComplex

end CategoryTheory
